# Process Requirements Document (PRD) Checklist

Before submitting any PR or merging changes, verify the following pipeline requirements are met. This ensures the zero-parameter, zero-postulate rigor of the Universal Field Resonance Framework is upheld.

- [ ] **Zero Axioms**: Ensure no new `axiom` declarations have been introduced. The proof must rely entirely on constructive definitions and existing theorems.
- [ ] **Zero Sorry**: Ensure `sorry` is entirely removed from all proofs. We maintain a zero-tolerance policy for incomplete proofs.
- [ ] **No `native_decide`**: Ensure `native_decide` is not used in proofs.
- [ ] **Sync Modules**: Drift between the Lean compilation tree and directory contents is prevented by running `scripts/sync_modules.py`. This ensures `UFRF.lean` matches the filesystem (ignoring `.removed` or `.bak` files).
- [ ] **Run Verify Script**: `./scripts/verify.sh` completes successfully. (Checks for sorries and builds the project).
- [ ] **Run Certify Script**: `./scripts/certify.sh` completes successfully. (Deep audits for axioms and `native_decide`).
