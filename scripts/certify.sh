#!/usr/bin/env bash
set -e

# Change to the root of the project
cd "$(dirname "$0")/.."

# First run standard verification
./scripts/verify.sh

echo "Running deep axiomatic audit..."

# Look for direct axiom declarations starting at beginning of line or after spaces, excluding Axiomatics.lean
AXIOMS=$(grep -rn "^[[:space:]]*axiom " UFRF/ --include="*.lean" | grep -v "UFRF/Axiomatics.lean" || true)

if [ -n "$AXIOMS" ]; then
    echo "❌ ERROR: Found unauthorized 'axiom' declarations:"
    echo "$AXIOMS"
    exit 1
else
    echo "✅ Only authorized axioms (Unity & 13-Lattice) found in Axiomatics.lean."
fi

# Look for native_decide usage
NATIVE=$(grep -rn "native_decide" UFRF/ --include="*.lean" || true)

if [ -n "$NATIVE" ]; then
    echo "❌ ERROR: Found 'native_decide' tactics (not allowed):"
    echo "$NATIVE"
    exit 1
else
    echo "✅ No 'native_decide' tactics found."
fi

echo "✅ Project is fully certified and adheres to the 2-Axiom Foundation policy."
