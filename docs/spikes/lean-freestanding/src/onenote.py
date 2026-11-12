"""Leave one note segment: the one that holds the PVH entry.

Cloud Hypervisor's loader keeps the answer from the last PT_NOTE segment it
reads, so a later segment without the Xen note hides the entry. The other
note segments become PT_NULL. Nothing at run time reads them.
"""
import struct, sys
path = sys.argv[1]
b = bytearray(open(path, "rb").read())
phoff, = struct.unpack_from("<Q", b, 32)
phentsize, phnum = struct.unpack_from("<HH", b, 54)
kept = 0
for i in range(phnum):
    o = phoff + i * phentsize
    p_type, _, off, _, _, filesz = struct.unpack_from("<IIQQQQ", b, o)
    if p_type != 4:
        continue
    if b"Xen\0" in b[off:off + filesz]:
        kept += 1
    else:
        struct.pack_into("<I", b, o, 0)
if kept != 1:
    sys.exit(f"expected one segment with the Xen note, found {kept}")
open(path, "wb").write(b)
