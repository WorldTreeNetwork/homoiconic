#!/bin/sh
# Two guests run one program between them, and each records what it did. A
# program is handed to the serving guest over QUIC as bytes; its start requests
# go to the other guest. Both records are read off the serial ports and checked
# outside the guests: the two logs are combined into one schedule, that
# schedule is replayed on one machine, and each process is compared with what
# its guest reported.
#
# Each guest has its own entity key, made for this run, and allows only the
# names it should hear from: the serving guest allows the other guest and the
# client that hands it the program, the calling guest allows the serving one.
# A record names its two sides by entity name and is signed by its guest's
# key; the check outside refuses a record whose signature is not good.
#
# Then delivery order: one program, two settings of which pending send the
# receiving guest takes first, two records, two results, and each record
# replays to its own. Then records that were tampered with, each refused with
# the reason of the check that catches it.
set -eu
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
ROOT="$(CDPATH= cd -- "$HERE/.." && pwd)"
CH="${CLOUD_HYPERVISOR:-$HOME/ch54/cloud-hypervisor}"
OUT="$HERE/out-net"
W="$OUT/wire"
BR="ukbr$$"
TA="ukwa$$"
TB="ukwb$$"
CHA=192.168.249.2
CHB=192.168.249.3
HOSTIP=192.168.249.1
BUDGET=100000

[ -r /dev/kvm ] && [ -w /dev/kvm ]
"$CH" --version | grep -qx "cloud-hypervisor v54.0"
sh "$HERE/build-net.sh"
rm -rf "$W"
mkdir -p "$W"
( cd "$ROOT/kernel" && lake env lean CrossingContract.lean ) | tee "$W/contract.txt"
if grep -v "depends on axioms: \[propext\(, Classical.choice\)\?\(, Quot.sound\)\?\]$" "$W/contract.txt" | grep -q .; then
    echo "the crossing theorems name another axiom" >&2
    exit 1
fi
( cd "$ROOT/kernel" && lake env lean CrossCheck.lean ) > "$W/lean.txt"
if grep -q "^FAIL\|error" "$W/lean.txt" || [ "$(grep -c "^ok" "$W/lean.txt")" -ne 85 ]; then
    cat "$W/lean.txt" >&2
    exit 1
fi
echo "ok   two guests in one process: 85 checks"

( umask 077
  for k in a b host other; do head -c 32 /dev/urandom > "$W/key-$k"; done )
KA="$W/key-a"
KB="$W/key-b"
KH="$W/key-host"
NA="$("$OUT/entity" name "$KA")"
NB="$("$OUT/entity" name "$KB")"
NH="$("$OUT/entity" name "$KH")"
NO="$("$OUT/entity" name "$W/key-other")"

pa=
pb=
sudo ip link del "$TA" 2>/dev/null || true
sudo ip link del "$TB" 2>/dev/null || true
sudo ip link del "$BR" 2>/dev/null || true
sudo ip link add "$BR" type bridge
sudo ip addr add "$HOSTIP/24" dev "$BR"
sudo ip link set "$BR" up
sudo ip tuntap add dev "$TA" mode tap user "$(id -un)"
sudo ip tuntap add dev "$TB" mode tap user "$(id -un)"
sudo ip link set "$TA" master "$BR" up
sudo ip link set "$TB" master "$BR" up
sudo ip link set "$TA" promisc on
sudo ip link set "$TB" promisc on
stop() {
    [ -z "$pa" ] || kill "$pa" 2>/dev/null || true
    [ -z "$pb" ] || kill "$pb" 2>/dev/null || true
    [ -z "$pa" ] || wait "$pa" 2>/dev/null || true
    [ -z "$pb" ] || wait "$pb" 2>/dev/null || true
    pa=
    pb=
}
cleanup() {
    [ -z "${fp:-}" ] || kill "$fp" 2>/dev/null || true
    stop
    sudo ip link del "$TA" 2>/dev/null || true
    sudo ip link del "$TB" 2>/dev/null || true
    sudo ip link del "$BR" 2>/dev/null || true
}
trap cleanup EXIT
fail() {
    echo "FAIL $1" >&2
    exit 1
}

boot() {
    rm -f "$4"
    timeout "${LIFE:-180}" "$CH" --kernel "$OUT/reflect-net.elf" --initramfs "$5" --cpus boot=1 --memory size=512M \
        --serial "file=$4" --console off \
        --net "tap=$1,mac=$2" --cmdline "$3" >"$4.ch" 2>&1 &
}

await() {
    end=$(( $(date +%s) + $3 ))
    while [ "$(date +%s)" -lt "$end" ]; do
        if grep -q "$2" "$1" 2>/dev/null; then return 0; fi
        sleep 0.05
    done
    return 1
}

# run <name> <program.hom> <words for A> <words for B>
# Guest A serves and is given the program. Guest B calls A and starts with no
# process. Leaves <name>.a and <name>.b, the two records, and <name>.bytes.
run() {
    name="$1"
    "$OUT/reply" source "$2" > "$W/$name.bytes"
    boot "$TA" 02:00:00:00:00:02 "reflect.ip=$CHA reflect.port=4444 reflect.wire_port=4446 reflect.allow=$NB,$NH $3" "$W/$name-a.log" "$KA"
    pa=$!
    await "$W/$name-a.log" "reflect: wire 4446" 60 || fail "$name: guest A did not come up"
    "$OUT/quic-client" "$CHA" 4446 "$BUDGET" "$W/$name.bytes" "$KH" "$NA" > "$W/$name.given" || fail "$name: the program was not taken"
    fp=
    if [ -n "${FLOOD:-}" ]; then
        # The host fills guest A's first-flight pool with first flights of
        # its own for as long as the run lasts, so every exchange guest B
        # opens finds it full and goes through a Retry (add-quic-admission).
        : > "$W/none.kept"
        "$OUT/quic-client" "$CHA" 4446 1 "$W/$name.bytes" "$W/key-other" "$NA" flood "$HOSTIP" 40 2000 "$W/none.kept" \
            2> "$W/$name.flood" &
        fp=$!
        sleep 0.5
    fi
    boot "$TB" 02:00:00:00:00:03 "reflect.ip=$CHB reflect.port=4444 reflect.peer=$CHA:4446 reflect.allow=$NA $4" "$W/$name-b.log" "$KB"
    pb=$!
    # Under the flood the run must close while the flood still runs.
    await "$W/$name-a.log" "reflect: cross done" "$([ -n "$fp" ] && echo 30 || echo "${WAIT:-90}")" || { cat "$W/$name-a.log" "$W/$name-b.log" >&2; fail "$name: guest A did not close"; }
    await "$W/$name-b.log" "reflect: cross done" "${WAIT:-30}" || { cat "$W/$name-a.log" "$W/$name-b.log" >&2; fail "$name: guest B did not close"; }
    stop
    if [ -n "$fp" ]; then
        # It heard Retries of its own: the first-flight pool was full.
        wait "$fp" || fail "$name: the flood did not run"
        fp=
        cat "$W/$name.flood"
        grep -q "heard [1-9][0-9]* Retries" "$W/$name.flood" || fail "$name: the first-flight pool was never full"
    fi
    grep -qx "reflect: entity $NA" "$W/$name-a.log" || fail "$name: guest A is not the entity of its key"
    grep -qx "reflect: entity $NB" "$W/$name-b.log" || fail "$name: guest B is not the entity of its key"
    sed -n 's/^reflect: cross \(\(sig\|form\|me\|peer\|budget\|own\|entry\|head\|proc\|error\) .*\)$/\1/p' "$W/$name-a.log" > "$W/$name.a"
    sed -n 's/^reflect: cross \(\(sig\|form\|me\|peer\|budget\|own\|entry\|head\|proc\|error\) .*\)$/\1/p' "$W/$name-b.log" > "$W/$name.b"
}

# accepted <name> <text>...: the records of <name> are accepted, and the
# replay holds every text.
accepted() {
    name="$1"
    shift
    "$OUT/cross-check" check "$W/$name.bytes" "$W/$name.a" "$W/$name.b" > "$W/$name.check" || { cat "$W/$name.check" >&2; fail "$name: the record was refused"; }
    for text in "$@"; do
        grep -qxF "$text" "$W/$name.check" || { cat "$W/$name.check" >&2; fail "$name: no line '$text'"; }
    done
    echo "ok   $name: accepted; $*"
}

# refused <what> <reason> <program> <record a> <record b>
refused() {
    if "$OUT/cross-check" check "$3" "$4" "$5" > "$W/refused.txt"; then
        cat "$W/refused.txt" >&2
        fail "$1: accepted"
    fi
    grep -qxF "refused: $2" "$W/refused.txt" || { cat "$W/refused.txt" >&2; fail "$1: not refused with '$2'"; }
    echo "ok   $1: refused: $2"
}

EX="$ROOT/examples"

# Each guest pins the other. B expects another name than A's: B refuses A and
# sends no batch. Then A does not allow B: A takes none of B's handshake, and
# B gets no answer. Neither run closes.
pinned() {
    boot "$TA" 02:00:00:00:00:02 "reflect.ip=$CHA reflect.port=4444 reflect.wire_port=4446 reflect.allow=$1" "$W/pin-a.log" "$KA"
    pa=$!
    await "$W/pin-a.log" "reflect: wire 4446" 60 || fail "pinned: guest A did not come up"
    boot "$TB" 02:00:00:00:00:03 "reflect.ip=$CHB reflect.port=4444 reflect.peer=$CHA:4446 reflect.allow=$2" "$W/pin-b.log" "$KB"
    pb=$!
    await "$W/pin-b.log" "^reflect: $3\$" 60 || { cat "$W/pin-b.log" >&2; fail "guest B did not say '$3'"; }
    sleep 1
    if grep -q "reflect: cross " "$W/pin-a.log" "$W/pin-b.log"; then fail "a guest ran a crossing with a peer it should not have"; fi
    stop
}
pinned "$NB,$NH" "$NO" "the peer is not allowed"
echo "ok   a guest that expects another name refuses its peer"
pinned "$NO,$NH" "$NA" "the peer gave no answer"
echo "ok   a guest its peer does not allow gets no answer"

# A function crosses with a reply name, keeps running on the other guest,
# starts a process of its own there, and both send back.
run reply "$EX/cross-reply.hom" "reflect.spawn=far" ""
grep -qx "me $NA" "$W/reply.a" && grep -qx "peer $NB" "$W/reply.a" || fail "A's record does not name the two entities"
grep -qx "me $NB" "$W/reply.b" && grep -qx "peer $NA" "$W/reply.b" || fail "B's record does not name the two entities"
echo "ok   each record names its guest and its peer by entity name"
accepted reply "process 0: [20, 22]; holds [#0]" "process 1: 7; holds [#0]" "process 2: 9; holds [#0]" "places a: [0]" "places b: [1, 2]"

# A name crosses in a message, and the answer comes back on it.
# The same run while the host floods guest A: guest B's exchanges each
# answer a Retry, and the records are the same.
FLOOD=1 run flooded "$EX/cross-reply.hom" "reflect.spawn=far" ""
accepted flooded "process 0: [20, 22]; holds [#0]" "process 1: 7; holds [#0]" "process 2: 9; holds [#0]" "places a: [0]" "places b: [1, 2]"

run name "$EX/cross-name.hom" "reflect.spawn=far" ""
accepted name "process 0: 5; holds [#2, #0]" "process 1: []; holds [#2, #0]"

# Delivery order. Both senders run on B and both sends are pending on A; A
# takes the oldest first, or the newest.
run old "$EX/cross-race.hom" "reflect.spawn=far reflect.take=old" ""
accepted old "schedule: [[0, 0, 0], [1, 0], [1, 0], [2, 1, 0], [2, 2, 0]]" "process 0: [1, 2]; holds [#0]"
run new "$EX/cross-race.hom" "reflect.spawn=far reflect.take=new" ""
accepted new "schedule: [[0, 0, 0], [1, 0], [1, 0], [2, 2, 0], [2, 1, 0]]" "process 0: [2, 1]; holds [#0]"
cmp -s "$W/old.bytes" "$W/new.bytes" || fail "the two runs had two programs"
if cmp -s "$W/old.a" "$W/new.a"; then fail "the two orders gave one record"; fi
grep -q "^proc \[1, 2\]; holds \[#0\]; root [0-9a-f]*$" "$W/old.a" || fail "guest A did not report [1, 2]"
grep -q "^proc \[2, 1\]; holds \[#0\]; root [0-9a-f]*$" "$W/new.a" || fail "guest A did not report [2, 1]"
echo "ok   one program, two delivery orders, two records, and each replays to its own result"

# Nesting deeper than the native stack (homoiconic-q59.72). The program builds
# data nested 960000 deep and a quoted program nested 288000 deep over 24
# turns, starts the program on the data on its own guest, and compares the
# data with itself. Reading the program back, compiling it, finding the names
# the data hands over and comparing recursed once for each level and ended the
# guest in the report of a full stack. Each is a walk now, on the guest and in
# the replay of the check.
BUDGET=10000000
run deep "$EX/cross-deep.hom" "reflect.turn=4000000 reflect.hold=16000000" "reflect.turn=4000000 reflect.hold=16000000"
BUDGET=100000
if grep -q "processor fault\|INTERNAL PANIC" "$W/deep-a.log" "$W/deep-b.log"; then fail "deep: a guest stopped"; fi
accepted deep "process 1: 7; holds [#48]"
grep -q "^process 0: 1; holds \[#48, #46, " "$W/deep.check" || { cat "$W/deep.check" >&2; fail "deep: process 0 did not compare the data with itself"; }
echo "ok   a guest starts a program nested 288000 deep on data nested 960000 deep and compares the data"

# Tampered records, from the real guests' records of the run `old`.
P="$W/old.bytes"
A="$W/old.a"
B="$W/old.b"
# Line numbers count the `sig` line, so entry k of a record is line k + 5.
entry() { grep -n "^entry " "$1" | sed -n "$(( $2 + 1 ))p" | cut -d: -f1; }
sign() { "$OUT/cross-check" sign "$1" "$2" > "$3"; }
lie() { "$OUT/cross-check" reseal "$2" > "$3.unsigned"; sign "$1" "$3.unsigned" "$3"; }
l5=$(entry "$A" 5); l6=$(entry "$A" 6)
awk -v x="$l5" -v y="$l6" '{ line[NR] = $0 } END { for (i = 1; i <= NR; i++) print (i == x ? line[y] : i == y ? line[x] : line[i]) }' "$A" > "$W/t-moved.raw"
sed "$(entry "$B" 2)d" "$B" > "$W/t-dropped.raw"
sed "${l5}p" "$A" > "$W/t-twice.raw"
sed "${l6}d" "$A" > "$W/t-short.raw"
# By someone who has no key: the bytes change and the signature does not.
refused "an entry moved, by another hand" "record a: the signature is not valid" "$P" "$W/t-moved.raw" "$B"
refused "an entry dropped, by another hand" "record b: the signature is not valid" "$P" "$A" "$W/t-dropped.raw"
refused "an entry repeated, by another hand" "record a: the signature is not valid" "$P" "$W/t-twice.raw" "$B"
refused "the last entry dropped, by another hand" "record a: the signature is not valid" "$P" "$W/t-short.raw" "$B"
sed 1d "$A" > "$W/t-nosig.a"
refused "a record with no signature" "record a: it is not signed" "$P" "$W/t-nosig.a" "$B"
sign "$W/key-other" "$A" "$W/t-other.a"
refused "a record signed by another entity" "record a: it is not signed by the entity it names" "$P" "$W/t-other.a" "$B"
# By the guest itself, which signs what it changed. The chain as recorded: an
# entry moved, dropped from the middle, repeated, and dropped from the end.
sign "$KA" "$W/t-moved.raw" "$W/t-moved.a"
refused "an entry moved" "log a: entry 5 does not name the entry before it" "$P" "$W/t-moved.a" "$B"
sign "$KB" "$W/t-dropped.raw" "$W/t-dropped.b"
refused "an entry dropped" "log b: entry 2 does not name the entry before it" "$P" "$A" "$W/t-dropped.b"
sign "$KA" "$W/t-twice.raw" "$W/t-twice.a"
refused "an entry repeated" "log a: entry 6 does not name the entry before it" "$P" "$W/t-twice.a" "$B"
sign "$KA" "$W/t-short.raw" "$W/t-short.a"
refused "the last entry dropped" "log a: the head is not its last entry" "$P" "$W/t-short.a" "$B"
# The chain made again too: the merge, the replay and the comparison each
# refuse what only they can see.
lie "$KA" "$W/t-twice.raw" "$W/t-twice-lie.a"
refused "a taking repeated, chain made again" "the logs do not combine" "$P" "$W/t-twice-lie.a" "$B"
lie "$KA" "$W/t-short.raw" "$W/t-short-lie.a"
refused "a taking dropped, chain made again" "the logs do not combine" "$P" "$W/t-short-lie.a" "$B"
sed "$(entry "$B" 5)d" "$B" > "$W/t-noack.raw"
lie "$KB" "$W/t-noack.raw" "$W/t-noack-lie.b"
refused "an acknowledgement dropped, chain made again" "the logs do not combine" "$P" "$A" "$W/t-noack-lie.b"
sed "$(entry "$A" 0)p" "$A" > "$W/t-event.raw"
lie "$KA" "$W/t-event.raw" "$W/t-event-lie.a"
refused "a local event repeated, chain made again" "[0, 0, 0] cannot happen" "$P" "$W/t-event-lie.a" "$B"
lie "$KA" "$W/t-moved.raw" "$W/t-moved-lie.a"
refused "the takings in the other order, chain made again" "the acknowledgements of b are not the order a took them in" "$P" "$W/t-moved-lie.a" "$B"
# A record made again and signed is still read: the refusals above are of
# what changed, not of the remaking.
lie "$KA" "$A" "$W/t-same-lie.a"
"$OUT/cross-check" check "$P" "$W/t-same-lie.a" "$B" > "$W/same.txt" || { cat "$W/same.txt" >&2; fail "a record made again unchanged was refused"; }
echo "ok   a record made again unchanged and signed is accepted"
# One run's record with another program, and with a guest's record of
# another program's run.
refused "another program" "[1, 0] cannot happen" "$W/name.bytes" "$A" "$B"
refused "a record of another run" "the logs do not combine" "$P" "$A" "$W/reply.b"
# harden-crossing. A record of one delivery order beside the other guest's
# record of the other order.
refused "records of two delivery orders" "the acknowledgements of b are not the order a took them in" "$P" "$W/old.a" "$W/new.b"
# A budget above the record's own limits, signed by its guest.
sed 's/^own 100000000 /own 99999 /' "$B" | sed 1d > "$W/t-own.raw"
sign "$KB" "$W/t-own.raw" "$W/t-own.b"
refused "a budget above its own limits" "record b: its budget is above its own limits" "$P" "$A" "$W/t-own.b"
# refusedStart <what> <start of the reason> <program> <a> <b>
refusedStart() {
    if "$OUT/cross-check" check "$3" "$4" "$5" > "$W/refused.txt"; then
        cat "$W/refused.txt" >&2
        fail "$1: accepted"
    fi
    grep -qF "refused: $2" "$W/refused.txt" || { cat "$W/refused.txt" >&2; fail "$1: not refused with '$2...'"; }
    echo "ok   $1: refused: $2..."
}
# full <name> <side>: the check says the side was full, and no guest stopped.
full() {
    grep -q "^full $2: entry [0-9]*, [0-9]* cells counted$" "$W/$1.check" || { cat "$W/$1.check" | head -20 >&2; fail "$1: $2 was not full"; }
    if grep -q "processor fault\|INTERNAL PANIC" "$W/$1-a.log" "$W/$1-b.log"; then fail "$1: a guest stopped"; fi
    echo "ok   $1: $2 is full, and no guest stopped"
}

# Budgets are the guest's own (homoiconic-q59.79). B allows anything: both
# run with what the program came with. B allows less: both run with B's.
run huge "$EX/cross-reply.hom" "reflect.spawn=far" "reflect.budget=18446744073709551615 reflect.turn=18446744073709551615"
grep -qx "budget 100000 500000" "$W/huge.a" && grep -qx "budget 100000 500000" "$W/huge.b" || fail "huge: the budgets are not A's"
grep -qx "own 18446744073709551615 18446744073709551615 2000000" "$W/huge.b" || fail "huge: B's own limits are not in its record"
accepted huge "process 0: [20, 22]; holds [#0]" "budget 100000 steps, 500000 cells"
run lower "$EX/cross-reply.hom" "reflect.spawn=far" "reflect.budget=50000 reflect.turn=300000"
grep -qx "budget 50000 300000" "$W/lower.a" && grep -qx "budget 50000 300000" "$W/lower.b" || fail "lower: the budgets are not B's"
accepted lower "process 0: [20, 22]; holds [#0]" "budget 50000 steps, 300000 cells"

# What a guest holds (homoiconic-q59.71). A process that keeps more on every
# turn without end; processes started on B that each keep a turn's worth; a
# log that grows without end on its cap; the largest local start.
run grow "$EX/cross-grow-forever.hom" "" ""
accepted grow "places b: []"
full grow a
BUDGET=10000000
run fan "$EX/cross-fan.hom" "reflect.spawn=far" ""
accepted fan "places a: [0]"
full fan b
run worst "$EX/cross-worst.hom" "" ""
accepted worst "places a: [0, 1]"
full worst a
BUDGET=100000
WAIT=400 LIFE=600 run chatter "$EX/cross-chatter.hom" "" ""
accepted chatter "places b: []"
full chatter a
grep -q "^full a: entry 60000, " "$W/chatter.check" || fail "chatter: A was not stopped at the cap"
echo "ok   chatter: the log stops at its cap, 60000 entries"
# The hold undone: the same growing process ends the guest.
boot "$TA" 02:00:00:00:00:02 "reflect.ip=$CHA reflect.port=4444 reflect.wire_port=4446 reflect.allow=$NB,$NH reflect.hold=18446744073709551615" "$W/panic-a.log" "$KA"
pa=$!
await "$W/panic-a.log" "reflect: wire 4446" 60 || fail "panic: guest A did not come up"
"$OUT/reply" source "$EX/cross-grow-forever.hom" > "$W/panic.bytes"
"$OUT/quic-client" "$CHA" 4446 "$BUDGET" "$W/panic.bytes" "$KH" "$NA" > "$W/panic.given" || fail "panic: the program was not taken"
boot "$TB" 02:00:00:00:00:03 "reflect.ip=$CHB reflect.port=4444 reflect.peer=$CHA:4446 reflect.allow=$NA" "$W/panic-b.log" "$KB"
pb=$!
await "$W/panic-a.log" "INTERNAL PANIC: out of memory" 240 || { tail -5 "$W/panic-a.log" >&2; fail "panic: with its hold at the largest, guest A did not run out of memory"; }
stop
echo "ok   with its hold at the largest, the growing process ends guest A in INTERNAL PANIC: out of memory"

# What the check compares (homoiconic-q59.69). A race on one guest whose two
# deliveries leave the same lines; swapped and signed again, the roots differ.
run hidden "$EX/cross-hidden.hom" "" ""
accepted hidden "places a: [0, 1, 2]"
l3=$(entry "$W/hidden.a" 3); l4=$(entry "$W/hidden.a" 4)
awk -v x="$l3" -v y="$l4" '{ line[NR] = $0 } END { for (i = 1; i <= NR; i++) print (i == x ? line[y] : i == y ? line[x] : line[i]) }' "$W/hidden.a" > "$W/t-hidden.raw"
lie "$KA" "$W/t-hidden.raw" "$W/t-hidden-lie.a"
refusedStart "a different run of the same program, its state as it was, re-signed" "process 0 (a 0): reported waiting on [2, #0]; holds [#0]; root " "$W/hidden.bytes" "$W/t-hidden-lie.a" "$W/hidden.b"
echo "wire guests ok"
