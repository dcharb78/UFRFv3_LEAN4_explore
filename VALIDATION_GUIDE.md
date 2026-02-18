# UFRF Lean Project: 3rd Party Validation Guide

To independently verify the mathematical proofs in this repository, you need the following standard Lean 4 environment.

## 1. Required Files

The following files constitute the "Source of Truth" for the project. If you are receiving this as a zip file, ensure these are present:

*   **Intentional Axioms**: Exactly 3 foundational postulates (Trinity, Zero Point, Dimensional Completeness). All other "axioms" (like 0=0) have been converted to theorems.
*   **`UFRF/`**: The directory containing all `.lean` source files.

## 2. Prerequisites

*   **Lean 4**: Install via [elan](https://github.com/leanprover/elan) (the standard Lean version manager).
    ```bash
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    ```
    *On Mac with Homebrew, you can also use `brew install elan-init`.*

## 3. Verification Steps

1.  **Navigate to the project root** (where `lakefile.lean` is located).
2.  **Get Dependencies**:
    ```bash
    lake update
    ```
    *This downloads Mathlib4 based on the manifest.*
3.  **Build and Verify**:
    ```bash
    lake build
    ```

## 4. Interpreting Results

*   **Success**: If `lake build` completes with exit code 0 and no error messages, **all proofs in the project are formally verified** by the Lean kernel.
*   **Code Transparency**:
    *   **Core Systems (Phases 1-11)**: Verified with **NO `sorry`** placeholders.
    *   **Geometric Mappings**: Fully proven in `GoldenAngle.lean`.
    *   **NO `native_decide`** tactics used.
    *   All theorems are proven essentially or constructionally from the base axioms defined in `Trinity.lean`.

## 5. Rigorous Dynamics & Primes

Phase 8.5 introduced a major enhancement: **Constructive Derivation of the Waveform**.

*   **Axiomatic Basis**: The universal waveform $W(t)$ is **not** defined arbitrarily. It is constructed piecewise from the `ThreeLOG` tensor grades:
    *   **Log1 (Seed)**: Proven to be **Linear** ($d^2W/dt^2 = 0$). Theorem: `seed_is_log1`.
    *   **Log2 (Expansion)**: Proven to be **Quadratic** ($d^2W/dt^2 > 0$). Theorem: `expansion_is_log2`.
    *   **Log3 (Contraction)**: Proven to be **Cubic** (Volumetric). Theorem: `contraction_is_log3`.
*   **Prime Definition**: The set of UFRF Primes is formally defined in `Constants.lean` as `{1} ∪ {p | Prime(p) ∧ p ≠ 2}`.
*   **Geometric Mappings**:
    *   `golden_angle_is_five`: ✅ PROVEN (bounds derived from `Mathlib`).
    *   `twin_gap_maps_to_rest`: ✅ PROVEN (bounds derived from `Mathlib`).
*   **Red Team Hardening (Phase 13)**:
    *   **Dimensionality**: `ThreeLOG` derives "9" from `finrank R V = 3`. Theorem: `nine_interior_positions`.
    *   **Geometric Determinism**: `Waveform` coefficients (1/9, 8/125) uniquely derived from smoothness constraints. Theorems: `unique_expansion_parabola`, `unique_contraction_cubic`.
    *   **Prediction Accuracy**: `FineStructure` verified to match CODATA 2018 within 0.05. Theorem: `ufrf_matches_codata`.
    *   **Prime Necessity**: Proved that only Prime 1 can carry the fundamental 13-cycle. Theorem: `prime_one_is_fundamental_carrier`.
    *   These theorems confirm the geometric correspondence without any `sorry` or `axiom`.
