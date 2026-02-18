# AngularEmbedding - The Rod and Staff

## Overview
The Rod (polarity axis) and Staff (observer axis) are orthogonal, generating the cross-sectional circle S¹ that becomes the poloidal axis of the Torus.

## Key Definitions

### `rod_angle` and `staff_angle`
```lean
noncomputable def rod_angle : ℝ := 0
noncomputable def staff_angle : ℝ := π / 2
```

The Rod is at 0°, the Staff is at 90°.

---

## Proven Theorems

### **Theorem: Observer is Orthogonal**
```lean
theorem observer_is_orthogonal : 
    staff_angle - rod_angle = π / 2
```
**Proof**: `norm_num`

**Significance**: The observer (Staff) is perpendicular to the polarity (Rod), establishing the fundamental orthogonality that generates the S¹ cross-section.

---

### **Theorem: Rod is Zero**
```lean
theorem rod_is_zero : rod_angle = 0
```
**Proof**: `rfl`

---

### **Theorem: Staff is Pi Half**
```lean
theorem staff_is_pi_half : staff_angle = π / 2
```
**Proof**: `rfl`

---

## Physical Interpretation

- **Rod**: The polarity axis (expansion/contraction)
- **Staff**: The observer axis (neutral reference frame)
- **Orthogonality**: The 90° angle ensures the observer is independent of the polarity

This orthogonality is the geometric basis for the Torus topology—the Staff becomes the poloidal axis, and the Rod becomes the toroidal/radial axis.
