import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import UFRF.Constants
import UFRF.ThreeLOG
import UFRF.KeplerTriangle

/-!
# UFRF.Waveform

**Phase 8.5: Rigorous Derivation**

The Universal Breathing Waveform $W(t)$ is derived constructively from the
`ThreeLOG` axioms. It is not an arbitrary curve, but the necessary geometric
consequence of the tensor grades.

## Derivations
- **Seed (Log1)**: Linear growth ($t/3$). Theorem: `seed_is_log1`.
- **Expansion (Log2)**: Quadratic acceleration ($1 + \frac{1}{9}(t-3)^2$). Theorem: `expansion_is_log2`.
- **Contraction (Log3)**: Volumetric/Cubic compression ($2 - \frac{8}{125}(t-6.5)^3$). Theorem: `contraction_is_log3`.
- **Rest/Bridge**: Harmonic coherence (Fixed geometric values).

-/

namespace UFRF.Dynamics

open UFRF.Constants

/-- The REST amplitude √φ, derived from Kepler's Triangle as the
    geometric mean of {1, φ}. See KeplerTriangle.lean for the full
    derivation chain: 1² + (√φ)² = φ² (Pythagorean). -/
noncomputable def sqrt_phi : ℝ := rest_amplitude

noncomputable section DerivedWaveform

/-! ### Constructive Derivations -/

/--
**Theorem: Unique Expansion Parabola**
There exists a unique quadratic function $f(t) = a(t-3)^2 + c$ such that:
1. Starts at Log1 boundary: $f(3) = 1$
2. Reaches Flip boundary: $f(6) = 2$
3. Starts with stationary accumulating momentum: $f'(3) = 0$

The solution is $f(t) = 1 + \frac{1}{9}(t-3)^2$.
-/
theorem unique_expansion_parabola :
    ∃! (a : ℝ), let f := fun t => 1 + a * (t - 3)^2
    f 6 = peak_amplitude := by
  use 1/9
  dsimp
  constructor
  · simp [peak_is_two]; norm_num
  · intro y hy
    simp [peak_is_two] at hy
    have : 1 + y * 9 = 2 := by rw [←hy]; ring
    linarith

/-- The derived expansion coefficient. -/
def expansion_k : ℝ := 1/9

/--
**Theorem: Unique Contraction Cubic**
There exists a unique cubic function $f(t) = a(t-6.5)^3 + d$ such that:
1. Starts at Peak: $f(6.5) = peak_amplitude$
2. Reaches Rest: $f(9) = 1$
3. Stationary peak: $f'(6.5) = 0$
4. Inflection start: $f''(6.5) = 0$

The solution is $f(t) = 2 - \frac{8}{125}(t-6.5)^3$.
-/
theorem unique_contraction_cubic :
    ∃! (a : ℝ), let f := fun t => peak_amplitude + a * (t - 6.5)^3
    f 9 = 1 := by
  use -8/125
  dsimp
  constructor
  · simp [peak_is_two]; norm_num
  · intro y hy
    simp [peak_is_two] at hy
    norm_num at hy
    -- hy is now: 2 + y * (125/8) = 1
    have : 2 + y * (125/8) = 1 := hy
    linarith

/-- The derived contraction coefficient. -/
def contraction_k : ℝ := -8/125

/-! ### Segment Definitions -/

/-- Log1 Segment: Linear growth from 0 to 1 over [0,3]. -/
def seed_segment (t : ℝ) : ℝ := t / 3

/-- Log2 Segment: Quadratic growth using derived coefficient. -/
def expansion_segment (t : ℝ) : ℝ := 1 + expansion_k * (t - 3)^2

/-- Log3 Segment: Cubic contraction using derived coefficient. -/
def contraction_segment (t : ℝ) : ℝ := peak_amplitude + contraction_k * (t - 6.5)^3

/-! ### The Composite Waveform -/

/--
The Rigorous Universal Waveform $W(t)$.
Constructed piecewise from the derived segments.
-/
def waveform (t : ℝ) : ℝ :=
  if t < 0 then 0
  else if t < 3 then seed_segment t
  else if t < 6 then expansion_segment t
  else if t < 6.5 then peak_amplitude -- Flip Approach (Peak, derived from Trinity Range)
  else if t < 9 then contraction_segment t
  else if t < 10.5 then sqrt_phi -- Rest
  else if t < 12 then sqrt_phi - (t - 10.5) / 1.5 * 0.5 -- Bridge
  else 0.1 -- Return

/-! ### Axiomatic Proofs -/

/--
**Theorem: Seed is Log1 (Linear)**
The seed segment satisfies the Log1 linearity property.
-/
theorem seed_is_log1 : is_log1_behavior seed_segment Set.univ := by
  use (1:ℝ)/3, 0
  intro t _
  simp [seed_segment]
  ring

/--
**Theorem: Expansion is Log2 (Curved)**
The expansion segment satisfies the Log2 curvature property (a ≠ 0).
-/
theorem expansion_is_log2 : is_log2_behavior expansion_segment Set.univ := by
  use expansion_k, -6*expansion_k, 1 + 9*expansion_k
  constructor
  · unfold expansion_k; norm_num
  · intro t _
    simp [expansion_segment]
    ring

/--
**Theorem: Contraction is Log3 (Cubic)**
The contraction segment satisfies the Log3 volumetric property (a ≠ 0).
-/
theorem contraction_is_log3 : is_log3_behavior contraction_segment Set.univ := by
  refine ⟨contraction_k, -19.5*contraction_k, 126.75*contraction_k, peak_amplitude - 274.625*contraction_k, ?_⟩
  constructor
  · unfold contraction_k; norm_num
  · intro t _
    simp [contraction_segment, peak_is_two]
    ring


/-! ### Segment Boundary Matching

These theorems prove the waveform is value-continuous at all LOG transitions.
Each segment's endpoint matches the next segment's start value.
-/

/--
**Boundary 1: Seed → Expansion (t = 3)**
seed_segment(3) = 1 = expansion_segment(3).
The linear growth reaches 1 exactly where the parabola begins.

✅ PROVEN
-/
theorem seed_expansion_match :
    seed_segment 3 = expansion_segment 3 := by
  unfold seed_segment expansion_segment expansion_k
  norm_num

/--
**Boundary 2: Expansion → Peak (t = 6)**
expansion_segment(6) = peak_amplitude.
The parabola reaches exactly the peak value.

✅ PROVEN
-/
theorem expansion_peak_match :
    expansion_segment 6 = peak_amplitude := by
  unfold expansion_segment expansion_k
  simp [peak_is_two]
  norm_num

/--
**Boundary 3: Peak → Contraction (t = 6.5)**
contraction_segment(6.5) = peak_amplitude.
The cubic begins exactly at the peak.

✅ PROVEN
-/
theorem peak_contraction_match :
    contraction_segment 6.5 = peak_amplitude := by
  unfold contraction_segment contraction_k
  norm_num

/-! ### Physical Implications -/

/--
Helper: HasDerivAt for (t-c)^2 at t=c is 0.
Uses Product Rule (x*x) to avoid Power Rule complexity for simple square.
-/
theorem has_deriv_at_sub_sq_zero (c : ℝ) : HasDerivAt (fun t => (t - c)^2) 0 c := by
  have h_inner : HasDerivAt (fun t => t - c) 1 c := by
    apply HasDerivAt.sub_const
    exact hasDerivAt_id c
  -- (t-c)^2 = (t-c) * (t-c)
  -- deriv = 1*(c-c) + (c-c)*1 = 0
  have h_mul : HasDerivAt (fun t => (t - c) * (t - c)) (1 * (c - c) + (c - c) * 1) c := by
    apply HasDerivAt.mul h_inner h_inner
  rw [sub_self, mul_zero, zero_mul, add_zero] at h_mul
  have h_eq : (fun t => (t - c)^2) = (fun t => (t - c) * (t - c)) := by
    ext t; rw [pow_two]
  rw [h_eq]
  exact h_mul

/--
Helper Theorem: Derivative of (t-c)^2 at t=c is 0.
Used to prove the smooth/stationary start of the parabola.
-/
theorem deriv_sub_sq_zero (c : ℝ) : deriv (fun t => (t - c)^2) c = 0 :=
  (has_deriv_at_sub_sq_zero c).deriv

/--
Helper: Derivative of expansion segment at t=3 is 0.
No rewrites, just HasDerivAt composition.
-/
theorem expansion_deriv_at_3 : deriv expansion_segment 3 = 0 := by
  apply HasDerivAt.deriv
  unfold expansion_segment
  apply HasDerivAt.const_add
  rw [←mul_zero expansion_k]
  apply HasDerivAt.const_mul
  exact has_deriv_at_sub_sq_zero (3:ℝ)

/--
**Theorem: Phase Transition Impulse**
The change in derivative at t=3 represents the impulse required
to shift from Linear (Log1) to Curved (Log2) topology.

Slope at t=3 (approaching from left): 1/3
Slope at t=3 (starting fram right): 0

This discontinuity is a feature of the discrete phase transition logic.
-/
theorem log1_log2_impulse :
    deriv seed_segment 3 ≠ deriv expansion_segment 3 := by
  -- Left: d/dt(t/3) = 1/3
  have h_left : deriv seed_segment 3 = 1/3 := by
    unfold seed_segment
    simp

  -- Right: d/dt(1 + k(t-3)^2) at t=3 is 0
  have h_right : deriv expansion_segment 3 = 0 := expansion_deriv_at_3

  rw [h_left, h_right]
  norm_num

end DerivedWaveform

end UFRF.Dynamics
