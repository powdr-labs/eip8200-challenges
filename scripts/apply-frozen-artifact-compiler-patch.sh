#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Lake pins dependency revisions but has no declarative patch mechanism. This
# repository keeps reference bytecode frozen, so force the pinned Yul compiler
# to select its verified classic backend. The helper is idempotent for local
# builds and restored CI caches.
apply_frozen_artifact_patch() {
  local package_dir="$1"
  local patch_file="$2"

  if git -C "$package_dir" apply --check "$patch_file" >/dev/null 2>&1; then
    git -C "$package_dir" apply "$patch_file"
  elif git -C "$package_dir" apply --reverse --check "$patch_file" >/dev/null 2>&1; then
    return 0
  else
    echo "cannot apply $patch_file cleanly in $package_dir" >&2
    return 1
  fi
}

apply_frozen_artifact_patch \
  "$project_root/.lake/packages/yul-evm-compiler" \
  "$project_root/patches/frozen-artifacts/yul-compiler-classic-artifacts.patch"
