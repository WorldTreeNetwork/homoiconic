#!/bin/sh
# check-wire.sh on copies of the tree, each with one check of the record's
# signature undone in unikernel/cross-check.zig. Each must fail, at its test.
export PATH="$HOME/.elan/bin:$HOME/.local/share/mise/installs/zig/0.16.0/bin:$PATH"
SRC="$HOME/hom-ecaa6c8"
control() {
    what="$1"; old="$2"; new="$3"
    D="$HOME/hom-ecaa6c8-ctl"
    rm -rf "$D"; mkdir "$D"
    (cd "$SRC" && git archive --format=tar HEAD 2>/dev/null || tar -c --exclude=unikernel/out --exclude=unikernel/out-net --exclude=kernel/.lake --exclude="log-*" .) | tar -x -C "$D"
    python3 - "$D/unikernel/cross-check.zig" "$old" "$new" <<'PY'
import sys
p, old, new = sys.argv[1:4]
s = open(p).read()
assert s.count(old) == 1, "the source to undo is not there exactly once"
open(p, "w").write(s.replace(old, new))
PY
    echo "== undone: $what"
    if sh "$D/unikernel/check-wire.sh" > "$D/out.log" 2>&1; then
        echo "   NOT SHOWN: check-wire.sh still passes"
    else
        echo "   check-wire.sh fails:"
        grep "^FAIL\|^refused\|^accepted" "$D/out.log" | sed 's/^/   /'
        echo "   lines of ok before it: $(grep -c "^ok" "$D/out.log")"
    fi
    rm -rf "$D"
}
control "the signature is not verified" \
    'Ed.Signature.fromBytes(sig_bytes).verify(body, key) catch return refuse(who, "the signature is not valid");' \
    '_ = key;'
control "a record with no signature is taken as it stands" \
    'if (!std.mem.startsWith(u8, record, "sig ")) return refuse(who, "it is not signed");' \
    'if (!std.mem.startsWith(u8, record, "sig ")) return record;'
control "the signer need not be the entity the record names" \
    'if (!std.mem.startsWith(u8, body, want[0 .. 4 + name.len])) return refuse(who, "it is not signed by the entity it names");' \
    ''
echo "== done"
