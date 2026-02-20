#!/usr/bin/env bash
set -e

# Change to the root of the project
cd "$(dirname "$0")/.."

echo "Running sync_modules.py to prevent drift..."
python3 scripts/sync_modules.py

echo "Building UFRF..."
lake build

echo "Checking for sorry placeholders..."
SORRIES=$(grep -rn "sorry" UFRF/ --include="*.lean" | grep -v "UFRF/InverseLimit.lean" || true)

if [ -n "$SORRIES" ]; then
    echo "❌ ERROR: Found 'sorry' placeholders (excluding InverseLimit.lean structural sorry):"
    echo "$SORRIES"
    exit 1
else
    echo "✅ No 'sorry' placeholders found outside of permitted structural domains. Build verified."
fi
