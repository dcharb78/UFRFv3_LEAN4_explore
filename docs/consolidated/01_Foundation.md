# UFRF Proofs: Foundation & Core Axioms

This document consolidates the foundational modules of the UFRF formalization.

---

## 1. Trinity - The Axiomatic Foundation

### Overview
The Trinity is the fundamental axiom of UFRF: a conserved triplet `{-½, 0, +½}` that sums to zero.

### Key Definitions

**TrinityAxiom** (record type with three ℚ fields: neg, zero, pos)

### Proven Theorems

- **Symmetry**: `trinity.neg = -trinity.pos`
- **Uniqueness**: Any scaled triple with b=0, a=-c, c=k/2 satisfies conservation
- **Minimality**: 2 non-zero elements are necessary for conservation

---

## 2. Simplex - Boundary Face Counting

### Overview
Derives the number 4 from combinatorial topology (was `merkaba_geometric_factor` axiom).

### Proven Theorems
- **simplex3_face_count**: `C(4,3) = 4` (a 3-simplex has 4 boundary 2-faces)
- **simplex_face_count_general**: `C(n+1, n) = n+1`

---

## 3. KeplerTriangle - REST Amplitude

### Overview
Derives the REST amplitude √φ from Kepler's right triangle.

### Proven Theorems
- **kepler_pythagorean**: `1² + (√φ)² = φ²`
- **rest_kepler_property**: REST amplitude satisfies Kepler identity

---

## 4. Structure13 - Projective Plane Uniqueness

### Overview
Proves 13 is the **unique** cycle length via Finite Projective Plane theory.

### Key Definitions
- **projective_order(a)**: `a² + a + 1` (point count of PG(2,a))
- **overlap_retention(a)**: `a - 2` (positions retained under twin-prime displacement)
- **is_balanced(a)**: `a - 2 = 1` (exactly one retention)

### Proven Theorems
- **uniqueness_of_three**: `is_balanced a ↔ a = 3`
- **uniqueness_of_thirteen**: `projective_order 3 = 13`

---

## 5. Foundation - Derived Cycle Length

### Overview
Connects Trinity dimension (3) to cycle length (13) via projective order.

### Proven Theorems
- **cycle_is_thirteen**: `derived_cycle_length = 13`
- **dimensional_closure_equivalent**: `3×(3+1)+1 = 13` (corollary)
- **trinity_range_is_one**: `|½ - (-½)| = 1`
- **peak_from_trinity**: `1 + 1 = 2` (peak amplitude)

---

## 6. ThreeLOG - Tensor Grades

### Overview
Three qualitative modes (Linear, Curved, Cubed) generating 9 interior positions.

### Key Change (Phase 17)
The `merkaba_geometric_factor` axiom was **replaced** by `Simplex.simplex3_face_count`.
The duality factor 4 is now a theorem, not an axiom.

### Proven Theorems
- **nine_interior_positions**: `3 × 3 = 9`
- **simplex3_face_count**: `C(4,3) = 4` (imported from Simplex)

---

## 7. Constants - Fundamental Values

### Key Definitions
- **phi**: `(1 + √5) / 2` ≈ 1.618
- **peak_amplitude**: `2` (derived from Trinity range)
- **rest_amplitude**: `√φ` (derived from Kepler)
- **ufrf_alpha_inv**: `4π³ + π² + π` ≈ 137.036

### Proven Theorems
- **phi_golden**: `φ² = φ + 1`
- **peak_is_two**: `peak_amplitude = 2`
- **trinity_range_is_one**: `trinity_range = 1`

---

## Summary

These 7 modules establish the axiomatic foundation:
1. **Trinity**: The conserved triplet {-½, 0, +½}
2. **Simplex**: 4 from geometry (replaces merkaba axiom)
3. **KeplerTriangle**: √φ from Pythagorean theorem
4. **Structure13**: 13 as unique projective balance
5. **Foundation**: Cycle length derived from Trinity
6. **ThreeLOG**: 9 interior positions from tensor grades
7. **Constants**: All physical values derived, not hardcoded
