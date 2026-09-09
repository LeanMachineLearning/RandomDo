#!/usr/bin/env bash
#

cd "$(dirname "$0")/.." || exit 1

status=0
for script in scripts/check_*.py; do
  echo "== $script"
  python3 "$script" || status=1
done
exit $status
