BINARIES="redo redo-sources redo-targets"
SYMLINKS="redo-ifcreate redo-ifchange redo-always"

: ${DESTDIR:=NONE}
: ${PREFIX:=/usr}
: ${MANDIR:=$DESTDIR$PREFIX/share/man}
: ${BINDIR:=$DESTDIR$PREFIX/bin}

if [ "$DESTDIR" = "NONE" ]; then
	echo "$0: fatal: set DESTDIR before trying to install." >&2
	exit 99
fi

for binary in $BINARIES
do
    install -Dm0755 "$binary" "$BINDIR/$binary"
done

for symlink in $SYMLINKS
do
    ln -sf "$PREFIX"/bin/redo "$BINDIR/$symlink"
done
