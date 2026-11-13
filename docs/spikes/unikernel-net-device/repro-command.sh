#!/bin/sh
# Read-only access preflight. This is not the virtio device/packet spike.
# Invoke after restoring LAN access or providing the linked Framework host.
set -eu
HOST="${1:-framework}"
case "$HOST" in framework | morphie) ;; *) echo 'usage: repro-command.sh [framework|morphie]' >&2; exit 2 ;; esac
exec ssh -o BatchMode=yes -o ConnectTimeout=5 "$HOST" 'set -eu
    test "$(uname -sm)" = "Linux x86_64"
    test -r /dev/kvm && test -w /dev/kvm
    if command -v cloud-hypervisor >/dev/null 2>&1; then
        cloud-hypervisor --version
    else
        "$HOME/ch54/cloud-hypervisor" --version
    fi'
