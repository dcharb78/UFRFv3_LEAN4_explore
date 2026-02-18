import UFRF.Constants
import UFRF.BreathingCycle

namespace UFRF.GoldenAngle

-- The `<;>` in sqrt bounds is semantically needed (rw produces side goals).
set_option linter.unnecessarySeqFocus false

open UFRF.Constants
open BreathingCycle (in_position_bin)

/-!
# Golden Angle Mappings

Proving the geometric correspondence between the Golden Angle, 
the 13-Cycle, and Prime Gaps using exact Real ratios.
-/

/--
The Golden Angle position on the 13-cycle.
Angle = 360 / φ²
Position = (Angle / 360) * 13 = 13 / φ²
-/
noncomputable def golden_angle_position : ℝ := 13 / (phi ^ 2)

/--
**Theorem: Golden Angle maps to Position 5 (Rigorous)**
The golden angle position (~4.966) falls strictly within the 
Fundamental Phase Bin of Position 5 [4.5, 5.5).
-/
theorem golden_angle_in_pos_five_bin : 
    in_position_bin golden_angle_position 5 := by
  unfold in_position_bin golden_angle_position phi
  -- We need to prove: 4.5 ≤ 13/φ² < 5.5
  
  -- 1. Bounds for √5
  have h_sqrt5_lo : 2.236 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)] <;> norm_num
  have h_sqrt5_hi : Real.sqrt 5 < 2.237 := by
    rw [Real.sqrt_lt (by norm_num)] <;> norm_num
  have h_pos : 0 < 3 + Real.sqrt 5 := add_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))

  constructor
  · -- Lower Bound: 4.5 ≤ 13/φ²
    -- 13/φ² = 52/(3+√5)
    field_simp [h_pos]
    nlinarith
    
  · -- Upper Bound: 13/φ² < 5.5
    field_simp [h_pos]
    nlinarith

/--
**Theorem: Twin Prime Gap (2) maps to REST**
The gap of 2 projects to 2 * golden_angle_position ≈ 9.93.
The Rest phase is defined as [9, 10.5].
9.93 is well within this interval.
-/
theorem twin_gap_maps_to_rest : 
    9 < 2 * golden_angle_position ∧ 2 * golden_angle_position < 10.5 := by
  unfold golden_angle_position phi
  -- 2 * 13 / φ² = 52 / (3 + √5)
  have h_sqrt5_lo : 2.236 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)] <;> norm_num
  have h_sqrt5_hi : Real.sqrt 5 < 2.237 := by
    rw [Real.sqrt_lt (by norm_num)] <;> norm_num
  have h_pos : 0 < 3 + Real.sqrt 5 := add_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num))

  constructor
  · -- 9 < 52 / (3 + √5)
    field_simp [h_pos]
    nlinarith
  · -- 52 / (3 + √5) < 10.5
    field_simp [h_pos]
    nlinarith

end UFRF.GoldenAngle
