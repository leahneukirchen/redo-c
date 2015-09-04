/* An implementation of the redo build system
   in portable C with zero dependencies

   http://cr.yp.to/redo.html
   http://homepage.ntlworld.com/jonathan.deboynepollard/FGA/introduction-to-redo.html
   https://github.com/apenwarr/redo/blob/master/README.md
   http://news.dieweltistgarnichtso.net/bin/redo-sh.html

   To the extent possible under law,
   Christian Neukirchen <chneukirchen@gmail.com>
   has waived all copyright and related or neighboring rights to this work.

   http://creativecommons.org/publicdomain/zero/1.0/
*/

/*
##% cc -g -Os -Wall -Wextra -Wwrite-strings -o $STEM $FILE
*/

/*
current bugs:
  dependency-loop: unlimited recursion
    need locks

todo:
  test job server properly
*/

#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

// ---------------------------------------------------------------------------
// from musl/src/crypt/crypt_sha256.c

/* public domain sha256 implementation based on fips180-3 */

struct sha256 {
	uint64_t len;    /* processed message length */
	uint32_t h[8];   /* hash state */
	uint8_t buf[64]; /* message block buffer */
};

static uint32_t ror(uint32_t n, int k) { return (n >> k) | (n << (32-k)); }
#define Ch(x,y,z)  (z ^ (x & (y ^ z)))
#define Maj(x,y,z) ((x & y) | (z & (x | y)))
#define S0(x)      (ror(x,2) ^ ror(x,13) ^ ror(x,22))
#define S1(x)      (ror(x,6) ^ ror(x,11) ^ ror(x,25))
#define R0(x)      (ror(x,7) ^ ror(x,18) ^ (x>>3))
#define R1(x)      (ror(x,17) ^ ror(x,19) ^ (x>>10))

static const uint32_t K[64] = {
0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};

static void processblock(struct sha256 *s, const uint8_t *buf)
{
	uint32_t W[64], t1, t2, a, b, c, d, e, f, g, h;
	int i;

	for (i = 0; i < 16; i++) {
		W[i] = (uint32_t)buf[4*i]<<24;
		W[i] |= (uint32_t)buf[4*i+1]<<16;
		W[i] |= (uint32_t)buf[4*i+2]<<8;
		W[i] |= buf[4*i+3];
	}
	for (; i < 64; i++)
		W[i] = R1(W[i-2]) + W[i-7] + R0(W[i-15]) + W[i-16];
	a = s->h[0];
	b = s->h[1];
	c = s->h[2];
	d = s->h[3];
	e = s->h[4];
	f = s->h[5];
	g = s->h[6];
	h = s->h[7];
	for (i = 0; i < 64; i++) {
		t1 = h + S1(e) + Ch(e,f,g) + K[i] + W[i];
		t2 = S0(a) + Maj(a,b,c);
		h = g;
		g = f;
		f = e;
		e = d + t1;
		d = c;
		c = b;
		b = a;
		a = t1 + t2;
	}
	s->h[0] += a;
	s->h[1] += b;
	s->h[2] += c;
	s->h[3] += d;
	s->h[4] += e;
	s->h[5] += f;
	s->h[6] += g;
	s->h[7] += h;
}

static void pad(struct sha256 *s)
{
	unsigned r = s->len % 64;

	s->buf[r++] = 0x80;
	if (r > 56) {
		memset(s->buf + r, 0, 64 - r);
		r = 0;
		processblock(s, s->buf);
	}
	memset(s->buf + r, 0, 56 - r);
	s->len *= 8;
	s->buf[56] = s->len >> 56;
	s->buf[57] = s->len >> 48;
	s->buf[58] = s->len >> 40;
	s->buf[59] = s->len >> 32;
	s->buf[60] = s->len >> 24;
	s->buf[61] = s->len >> 16;
	s->buf[62] = s->len >> 8;
	s->buf[63] = s->len;
	processblock(s, s->buf);
}

static void sha256_init(struct sha256 *s)
{
	s->len = 0;
	s->h[0] = 0x6a09e667;
	s->h[1] = 0xbb67ae85;
	s->h[2] = 0x3c6ef372;
	s->h[3] = 0xa54ff53a;
	s->h[4] = 0x510e527f;
	s->h[5] = 0x9b05688c;
	s->h[6] = 0x1f83d9ab;
	s->h[7] = 0x5be0cd19;
}

static void sha256_sum(struct sha256 *s, uint8_t *md)
{
	int i;

	pad(s);
	for (i = 0; i < 8; i++) {
		md[4*i] = s->h[i] >> 24;
		md[4*i+1] = s->h[i] >> 16;
		md[4*i+2] = s->h[i] >> 8;
		md[4*i+3] = s->h[i];
	}
}

static void sha256_update(struct sha256 *s, const void *m, unsigned long len)
{
	const uint8_t *p = m;
	unsigned r = s->len % 64;

	s->len += len;
	if (r) {
		if (len < 64 - r) {
			memcpy(s->buf + r, p, len);
			return;
		}
		memcpy(s->buf + r, p, 64 - r);
		len -= 64 - r;
		p += 64 - r;
		processblock(s, s->buf);
	}
	for (; len >= 64; len -= 64, p += 64)
		processblock(s, p);
	memcpy(s->buf, p, len);
}

// ----------------------------------------------------------------------

int dir_fd = -1;
int dep_fd = -1;
int poolwr_fd = -1;
int poolrd_fd = -1;
int level = -1;
int implicit_jobs = 1;
int kflag, jflag, xflag, fflag;

static void
redo_ifcreate(char *target)
{
	dprintf(dep_fd, "-%s\n", target);
}

static char *
check_dofile(const char *fmt, ...)
{
	static char dofile[1024];

	va_list ap;
	va_start(ap, fmt);
	vsnprintf(dofile, sizeof dofile, fmt, ap);
	va_end(ap);

	if (access (dofile, F_OK) == 0) {
		return dofile;
	} else {
		redo_ifcreate(dofile);
		return 0;
	}
}

/*
dir/base.a.b
       will look for dir/base.a.b.do,
       dir/default.a.b.do, dir/default.b.do, dir/default.do,
       default.a.b.do, default.b.do, and default.do.

this function assumes no / in target
*/
static char *
find_dofile(char *target)
{
	char updir[1024];
	char *u = updir;
	char *dofile, *s;
	struct stat st, ost;

	dofile = check_dofile("./%s.do", target);
	if (dofile)
		return dofile;

	*u++ = '.';
	*u++ = '/';
	*u = 0;

	st.st_dev = ost.st_dev = st.st_ino = ost.st_ino = 0;
	
	while (1) {
		ost = st;

		if (stat(updir, &st) < 0)
			return 0;
		if (ost.st_dev == st.st_dev && ost.st_ino == st.st_ino)
			break;  // reached root dir, .. = .

		s = target;
		while (*s) {
			if (*s++ == '.') {
				dofile = check_dofile("%sdefault.%s.do", updir, s);
				if (dofile)
					return dofile;
			}
		}

		dofile = check_dofile("%sdefault.do", updir);
		if (dofile)
			return dofile;

		*u++ = '.';
		*u++ = '.';
		*u++ = '/';
		*u = 0;
	}

	return 0;
}

static int
envfd(const char *name)
{
	long fd;

	char *s = getenv(name);
	if (!s)
		return -1;
	
	fd = strtol(s, 0, 10);
	if (fd < 0 || fd > 255)
		fd = -1;
	
	return fd;
}

static void
setenvfd(const char *name, int i)
{
	char buf[16];
	snprintf(buf, sizeof buf, "%d", i);
	setenv(name, buf, 1);
}

static char *
hashfile(int fd)
{
	static char hex[16] = "0123456789abcdef";
	static char asciihash[65];

	struct sha256 ctx;
	off_t off = 0;
	char buf[4096];
	char *a;
	unsigned char hash[32];
	int i;
	ssize_t r;

	sha256_init(&ctx);

	while ((r = pread(fd, buf, sizeof buf, off)) > 0) {
		sha256_update(&ctx, buf, r);
		off += r;
	}
	
	sha256_sum(&ctx, hash);
	
	for (i = 0, a = asciihash; i < 32; i++) {
		*a++ = hex[hash[i] / 16];
		*a++ = hex[hash[i] % 16];
	}
	*a = 0;

	return asciihash;
}

static char *
targetchdir(char *target) {
	char *base = strrchr(target, '/');
	if (base) {
		int fd;
		*base = 0;
		fd = openat(dir_fd, target, O_RDONLY | O_DIRECTORY);
		*base = '/';
		fchdir(fd);
		close(fd);
		return base+1;
	} else {
		fchdir(dir_fd);
		return target;
	}
}

static char *
targetdep(char *target) {
	static char dep[1024];
	snprintf(dep, sizeof dep, ".%s.dep", target);
	return dep;
}

static int
sourcefile(char *target)
{
	target = targetchdir(target);
	return access(target, F_OK) == 0 && access(targetdep(target), F_OK) != 0;
}

static int
check_deps(char *target)
{
	char *depfile, *filename;
	FILE *f;
	int ok = 1;
	int fd;

	target = targetchdir(target);

	if (access(target, F_OK) != 0)
		return 0;

	depfile = targetdep(target);
	f = fopen(depfile, "r");
	if (!f)
		return 0;

	while (ok && !feof(f)) {
		char line[4096];
		if (fgets(line, sizeof line, f)) {
			line[strlen(line)-1] = 0; // strip \n
			switch (line[0]) {
			case '-':  // must not exist 
				if (access(line+1, F_OK) == 0)
					ok = 0;
				break;
			case '=':  // compare hash
				filename = line + 1 + 64 + 1;
				fd = open(filename, O_RDONLY);
				if (fd < 0) {
					ok = 0;
				} else {
					char *hash = hashfile(fd);
					if (strncmp(line+1, hash, 64) != 0)
						ok = 0;
					close(fd);
				}
				// hash is good, recurse into dependencies
				if (ok && strcmp(target, filename) != 0 &&
				    !sourcefile(filename))
					ok = check_deps(filename);
				break;
			case '!':  // always rebuild
			default:  // dep file broken, lets recreate it
				ok = 0;
			}
		} else {
			if (!feof(f)) {
				ok = 0;
				break;
			}
		}
	}

	fclose(f);

	return ok;
}

void
vacate(int implicit) {
	if (implicit)
		implicit_jobs++;
	else
		write(poolwr_fd, "\0", 1);
}

struct job {
	struct job *next;
	pid_t pid;
	char *target, *temp_depfile, *temp_target;
	int implicit;
};
struct job *jobhead;

static void
insert_job(struct job *job)
{
	job->next = jobhead;
	jobhead = job;
}

static void
remove_job(struct job *job)
{
	if (jobhead == job)
		jobhead = jobhead->next;
	else {
		struct job *j = jobhead;
		while (j->next != job)
			j = j->next;
		j->next = j->next->next;
	}
}

static struct job *
find_job(pid_t pid)
{
	struct job *j;

	for (j = jobhead; j; j = j->next) {
		if (j->pid == pid)
			return j;
	}

	return 0;
}

static struct job *
run_script(char *target, int implicit)
{
	char temp_depfile[] = ".dep.XXXXXX";
	char temp_target[] = ".target.XXXXXX";
	char *orig_target = target;
	int old_dep_fd = dep_fd;
	int fd;
	char *dofile;
	pid_t pid;

	target = targetchdir(target);

	dep_fd = mkstemp(temp_depfile);

	fd = mkstemp(temp_target);
	close(fd);

	// TODO locking to detect parallel jobs building same target?

	dofile = find_dofile(target);
	if (!dofile) {
		fprintf(stderr, "no dofile for %s.\n", target);
		exit(1);
	}

	fd = open(dofile, O_RDONLY);
	dprintf(dep_fd, "=%s %s\n", hashfile(fd), dofile);
	close(fd);
	
	printf("redo%*.*s %s # %s\n", level*2, level*2, " ", orig_target, dofile);

	pid = fork();
	if (pid < 0) {
		perror("fork");
		vacate(implicit);
		exit(-1);
	} else if (pid == 0) { // child
/*
djb-style default.o.do:
   $1      foo.o
   $2      foo
   $3      whatever.tmp

   $1      all
   $2      all (!!)
   $3      whatever.tmp
*/
		int i;

		char *basename = strdup(target);
		if (strchr(basename, '.')) {
			for (i = strlen(basename)-1; i && basename[i] != '.'; i--)
				basename[i] = 0;
			basename[i--] = 0;
		}

		close(old_dep_fd);
		setenvfd("REDO_DEP_FD", dep_fd);
		setenvfd("REDO_LEVEL", level + 1);

		if (access (dofile, X_OK) != 0)  // run -x files with /bin/sh
			execl("/bin/sh", "/bin/sh", xflag > 0 ? "-ex" : "-e",
			    dofile, target, basename, temp_target, (char *) 0);
		else
			execl(dofile,
			    dofile, target, basename, temp_target, (char *) 0);
		vacate(implicit);
		exit(-1);
	} else {
		struct job *job = malloc (sizeof *job);
		if (!job)
			exit(-1);

		close(dep_fd);
		dep_fd = old_dep_fd;

		job->pid = pid;
		job->target = orig_target;
		job->temp_depfile = strdup(temp_depfile);
		job->temp_target = strdup(temp_target);
		job->implicit = implicit;

		insert_job(job);

		return job;
	}
}

static int
try_procure()
{
	if (implicit_jobs > 0) {
		implicit_jobs--;
		return 1;
	} else {
                struct pollfd p;

		if (poolrd_fd < 0)
			return 0;

                p.fd = poolrd_fd;
                p.events = POLLIN;

		if (poll(&p, 1, 0) > 0 && p.revents & POLLIN) {
			char buf[1];
			return read(poolrd_fd, &buf, 1) > 0;
		}
		return 0;
	}
}

static int
procure()
{
	if (implicit_jobs > 0) {
		implicit_jobs--;
		return 1;
	} else {
		char buf[1];
		return read(poolrd_fd, &buf, 1) > 0;
	}
}

void
create_pool()
{
	poolrd_fd = envfd("REDO_RD_FD");
	poolwr_fd = envfd("REDO_WR_FD");
	if (poolrd_fd < 0 || poolwr_fd < 0) {
		int jobs = envfd("JOBS");
		if (jobs > 1) {
			int i, fds[2];
			pipe(fds);
			poolrd_fd = fds[0];
			poolwr_fd = fds[1];
			
			for (i = 0; i < jobs-1; i++)
				vacate(0);

			setenvfd("REDO_RD_FD", poolrd_fd);
			setenvfd("REDO_WR_FD", poolwr_fd);
		} else {
			poolrd_fd = -1;
			poolwr_fd = -1;
		}
	}
}

static void
redo_ifchange(int targetc, char *targetv[])
{
	pid_t pid;
	int status;
	struct job *job;

	int targeti = 0;

	// XXX
	char skip[targetc];

	create_pool();

	// check all targets whether needing rebuild
	for (targeti = 0; targeti < targetc; targeti++)
		skip[targeti] = fflag > 0 ? 0 : check_deps(targetv[targeti]);
	
	targeti = 0;
	while (1) {
		int procured = 0;
		if (targeti < targetc) {
			char *target = targetv[targeti];

			if (skip[targeti] || sourcefile(target)) {
				targeti++;
				continue;
			}

			if (try_procure()) {
				procured = 1;
				targeti++;
				run_script(target, implicit_jobs >= 0);
			}
		}

		pid = waitpid(-1, &status, procured ? WNOHANG : 0);

		if (pid == 0)
			continue;  // nohang

		if (pid < 0) {
			if (errno == ECHILD && targeti < targetc)
				continue;   // no child yet???
			else
				break;   // no child left
		}

		if (WIFEXITED(status))
			status = WEXITSTATUS(status);

		job = find_job(pid);
		
		if (!job) {
			exit(-1);
		}
		remove_job(job);

		if (status > 0) {
			remove(job->temp_depfile);
			remove(job->temp_target);
		} else {
			struct stat st;
			char *target = targetchdir(job->target);
			char *depfile = targetdep(target);

			if (stat(job->temp_target, &st) == 0 &&
			    st.st_size > 0) {
				int dfd, tfd;

				dfd = open(job->temp_depfile, O_WRONLY|O_APPEND);
				tfd = open(job->temp_target, O_RDONLY);
				dprintf(dfd, "=%s@%s\n", hashfile(tfd), target);
				close(dfd);
				close(tfd);

				rename(job->temp_target, target);
			} else {
				remove(job->temp_target);
			}

			rename(job->temp_depfile, depfile);
		}

		vacate(job->implicit);
		
		if (kflag < 0 && status > 0) {
			printf("failed with status %d\n", status);
			exit(status);
		}
	}
}

static void
record_deps(int targetc, char *targetv[])
{
	int targeti = 0;
	int fd;

	dep_fd = envfd("REDO_DEP_FD");
	if (dep_fd < 0)
		return;

	for (targeti = 0; targeti < targetc; targeti++) {
		fd = open(targetv[targeti], O_RDONLY);
		if (fd < 0)
			continue;
		// here, we write out the unmodified target name!
		dprintf(dep_fd, "=%s!%s\n", hashfile(fd), targetv[targeti]);
		close(fd);
	}
}

int
main(int argc, char *argv[])
{
	char *program;
	int opt;

	dep_fd = envfd("REDO_DEP_FD");

	level = envfd("REDO_LEVEL");
	if (level < 0)
		level = 0;

	fflag = envfd("REDO_FORCE");
	kflag = envfd("REDO_KEEP_GOING");
	xflag = envfd("REDO_TRACE");

	if ((program = strrchr(argv[0], '/')))
		program++;
	else
		program = argv[0];

        while ((opt = getopt(argc, argv, "+kxfj:C:")) != -1) {
                switch (opt) {
                case 'k':
                        kflag = 1;
			setenvfd("REDO_KEEP_GOING", 1);
                        break;
                case 'x':
                        xflag = 1;
			setenvfd("REDO_TRACE", 1);
                        break;
                case 'f':
                        fflag = 1;
			setenvfd("REDO_FORCE", 1);
                        break;
                case 'j':
                        setenv("JOBS", optarg, 1);
                        break;
                case 'C':
			if (chdir(optarg) < 0) {
				perror("chdir");
				exit(-1);
			}
			break;
                default:
			fprintf(stderr, "usage: %s [-kfx] [-jN] [-Cdir] [TARGETS...]\n", program);
                        exit(1);
                }
        }
        argc -= optind;
        argv += optind;

        if (argc == 0) {
		argc = 1;
		argv[0] = (char *) "all";   // XXX safe?
        }

	dir_fd = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
	if (dir_fd < 0) {
		perror("dir open");
		exit(-1);
	}

	if (strcmp(program, "redo") == 0) {
		fflag = 1;
		redo_ifchange(argc, argv);
		procure();
	} else if (strcmp(program, "redo-ifchange") == 0) {
		redo_ifchange(argc, argv);
		record_deps(argc, argv);
		procure();
	} else if (strcmp(program, "redo-ifcreate") == 0) {
		int i;
		for (i = 0; i < argc; i++)
			redo_ifcreate(argv[i]);
	} else if (strcmp(program, "redo-always") == 0) {
		dprintf(dep_fd, "!\n");
	} else if (strcmp(program, "redo-hash") == 0) {
		printf("%s\n", hashfile(0));
	} else {
		fprintf(stderr, "not implemented %s\n", program);
		exit(-1);
	}

	return 0;
}
