#!/bin/sh
# Boot the image with a program's byte form given at boot. This is the launch
# the README documents, and the one the check uses.
#   sh unikernel/given.sh <bytes-file> [step-budget [levels [space]]]
# Environment: CLOUD_HYPERVISOR (default cloud-hypervisor), IMAGE (default
# unikernel/out/reflect.elf), SERIAL (Cloud Hypervisor's --serial, default tty).
#
# Cloud Hypervisor 54.0 loads the ELF file, then copies the --initramfs file to
# the top of the first memory region, rounded down to a page, without looking
# at where the ELF file lies. A file nearly as large as that region lands on
# the image before any of the image's code runs, and the image cannot refuse
# it: with 512 MiB, a file of 500 MiB ends in "InternalError" from the
# processor, an empty serial port and exit status 0 (unikernel/README.md). So
# the size is refused here, before the hypervisor starts. With the 512 MiB this
# launch gives, a file of up to 2 MiB lands at 510 MiB or above, far from the
# image at 16 MiB, and the image refuses anything larger in any case. The limit
# is 2 MiB, not more, because valid data of 4 MiB can need more memory than
# 512 MiB to read and print (unikernel/README.md).
set -eu
HERE="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
CH="${CLOUD_HYPERVISOR:-cloud-hypervisor}"
IMAGE="${IMAGE:-$HERE/out/reflect.elf}"
SERIAL="${SERIAL:-tty}"
limit=2097152
if [ $# -lt 1 ] || [ $# -gt 4 ]; then
    echo "usage: given.sh <bytes-file> [step-budget [levels [space]]]" >&2
    exit 2
fi
file="$1"
shift
[ -f "$file" ] && [ -r "$file" ] || { echo "given: cannot read $file as a file" >&2; exit 2; }
size="$(wc -c < "$file" | tr -d ' ')"
[ "$size" -le "$limit" ] || { echo "given: the program given at boot is larger than 2 MiB" >&2; exit 2; }
exec "$CH" --kernel "$IMAGE" --initramfs "$file" ${1+--cmdline "$*"} --cpus boot=1 --memory size=512M \
    --serial "$SERIAL" --console off
