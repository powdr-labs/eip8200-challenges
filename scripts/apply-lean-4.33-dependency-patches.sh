#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

apply_dependency_patch() {
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

apply_dependency_patch \
  "$project_root/.lake/packages/yul-evm-compiler" \
  "$project_root/patches/lean-4.33/yul-evm-compiler.patch"
