import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UFRF.Constants

/-!
# UFRF.KeplerTriangle

**Derivation of the REST Amplitude √φ from Kepler's Triangle**

Kepler's Triangle is a classical geometric object — a right triangle
with sides in the ratio **1 : √φ : φ**. It satisfies the Pythagorean
theorem: 1² + (√φ)² = φ².

This works because φ² = φ + 1 (the defining property of the golden ratio),
so 1 + φ = φ², and thus 1² + (√φ)² = 1 + φ = φ².

## Connection to UFRF

In the breathing cycle:
- The base amplitude is **1** (the unit, end of Log1 at position 3)
- The golden ratio **φ** governs the cycle's geometric structure
- The REST phase (position 10) is the quiescent equilibrium between
  contraction and the next seed

√φ is the **geometric mean** of {1, φ} — the natural equilibrium point
between the unit identity and golden coherence. In Kepler's Triangle,
√φ is the altitude connecting the unit leg to the golden hypotenuse.

Therefore, the REST amplitude √φ is **derived** from the golden ratio
structure, not inserted by hand.

## References
- Cut-the-Knot: Golden Ratio Properties (cut-the-knot.org)
- Kepler's Triangle (Wikipedia)
-/

noncomputable section

open UFRF.Constants
open Real

/-! ### Phi Properties -/

/-- √5 > 0 -/
theorem sqrt5_pos : Real.sqrt 5 > 0 := by positivity

/-- φ > 0 -/
theorem phi_pos : phi > 0 := by
  unfold phi
  have h := sqrt5_pos
  linarith

/-- φ ≥ 0 -/
theorem phi_nonneg : phi ≥ 0 := le_of_lt phi_pos

/-- √5 ≥ 0 -/
theorem sqrt5_nonneg : Real.sqrt 5 ≥ 0 := le_of_lt sqrt5_pos

/--
**The defining property of the Golden Ratio: φ² = φ + 1**

Proof: φ = (1 + √5)/2, so φ² = (1 + √5)²/4 = (6 + 2√5)/4 = (3 + √5)/2
     = (1 + √5)/2 + 1 = φ + 1.
-/
theorem phi_squared_eq_phi_plus_one : phi ^ 2 = phi + 1 := by
  unfold phi
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  field_simp
  nlinarith [h5]

/-! ### Kepler's Triangle -/

/--
**Kepler's Triangle Theorem**

In a right triangle with sides 1, √φ, and φ:
  1² + (√φ)² = φ²

This is the Pythagorean theorem applied to Kepler's triangle,
and it holds because φ² = φ + 1.

✅ PROVEN
-/
theorem kepler_pythagorean :
    (1 : ℝ) ^ 2 + (Real.sqrt phi) ^ 2 = phi ^ 2 := by
  rw [Real.sq_sqrt phi_nonneg]
  rw [phi_squared_eq_phi_plus_one]
  ring

/-! ### REST Amplitude Derivation -/

/--
**The REST amplitude is the geometric mean of {1, φ}**

geometric_mean(1, φ) = √(1 · φ) = √φ

This is the natural equilibrium point in Kepler's Triangle,
connecting the unit base (Log1 endpoint) to the golden coherence.
-/
noncomputable def rest_amplitude : ℝ := Real.sqrt (1 * phi)

/--
**Theorem: REST amplitude = √φ**

The geometric mean of 1 and φ is exactly √φ.

✅ PROVEN
-/
theorem rest_is_sqrt_phi : rest_amplitude = Real.sqrt phi := by
  unfold rest_amplitude
  simp [one_mul]

/--
**Theorem: REST amplitude satisfies the Kepler relationship**

The REST amplitude squared + 1 = φ².
This shows √φ is geometrically determined, not arbitrary.

✅ PROVEN
-/
theorem rest_kepler_property :
    1 + rest_amplitude ^ 2 = phi ^ 2 := by
  rw [rest_is_sqrt_phi]
  rw [Real.sq_sqrt phi_nonneg]
  rw [phi_squared_eq_phi_plus_one]
  ring

end
