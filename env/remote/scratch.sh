#!/usr/bin/env bash
# Mount the instance's local NVMe drives as /scratch (RAID0, ext4). Runs ON the instance.
#
# Instance storage is wiped when the instance STOPS (a reboot keeps it), so after a stop/start this
# recreates an empty /scratch and setup.sh re-syncs the sources. Nothing irreplaceable lives here.
# Safe to re-run. Refuses to touch any drive that has a filesystem/partition/RAID signature.
set -euo pipefail

DEVS=(/dev/nvme1n1 /dev/nvme2n1)
MD=/dev/md0
MNT=/scratch

if mountpoint -q "$MNT"; then
  echo "$MNT already mounted: $(df -h "$MNT" | tail -1)"; exit 0
fi

if [ ! -b "$MD" ]; then
  for d in "${DEVS[@]}"; do
    [ -b "$d" ] || { echo "missing $d"; exit 1; }
    grep -q "^${d}" /proc/mounts && { echo "$d is mounted; refusing"; exit 1; }
  done
  # Re-assemble an array this script made earlier (survives reboot), else create one on blank drives.
  if ! sudo -n mdadm --assemble "$MD" "${DEVS[@]}" 2>/dev/null; then
    for d in "${DEVS[@]}"; do
      if [ -n "$(sudo -n wipefs -n "$d")" ]; then echo "$d has signatures; refusing"; exit 1; fi
    done
    sudo -n mdadm --create "$MD" --level=0 --raid-devices=${#DEVS[@]} --run "${DEVS[@]}"
  fi
fi

sudo -n blkid -p "$MD" >/dev/null 2>&1 || sudo -n mkfs.ext4 -q -L scratch -E nodiscard,lazy_itable_init=1 "$MD"
sudo -n mkdir -p "$MNT"
sudo -n mount -o noatime "$MD" "$MNT"
sudo -n chown "$(id -u):$(id -g)" "$MNT"
echo "mounted $MNT: $(df -h "$MNT" | tail -1)"
