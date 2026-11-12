# Tasks

- [x] Owner: the user, 2026-11-12. Bead `homoiconic-q59.22`.
- [x] Record the intention to let Zig supply the fast Blake3 (`homoiconic-q59.20`).
- [x] `kernel/Wire/Blake3.lean`: the hash, from the specification.
- [x] `kernel/Wire/Cbor.lean`: byte strings in the reader and writer; reading data still refuses one.
- [x] `kernel/Wire/Piece.lean`: the byte form of a piece, and saving by cutting.
- [x] `kernel/Surface/Keep.lean`: a session for one turn against a store; the `reflect_keep_*` exports; `kernel_retain`.
- [x] `host/keep.zig`; `examples/keep.hom`.
- [x] `kernel/KeepCheck.lean` and the keep scenarios in `host/check.sh`; `sh host/check.sh` exits 0.
- [x] Advise by a reader from another model family. Send-back, 2026-11-12, two required fixes, both made; review in `reviews/`.
- [x] Fold. 2026-11-12: the three ADDED deltas are in `openspec/specs/`.
