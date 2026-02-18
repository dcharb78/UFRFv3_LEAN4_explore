import UFRF.Padic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Tactic

/-!
# UFRF.InverseLimit

**The One Ring: The Inverse Limit Construction**

The "One Ring" ℤ_[p] is not just a definition — it is the UNIQUE object
that unifies all the finite layers. It is the Inverse Limit of the tower.

ℤ_[p] ≅ lim ← ℤ/pⁿℤ
-/

section InverseLimit

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Helper: Projection from level n+1 to n. -/
def cast_down (n : ℕ) : ZMod (p ^ (n + 1)) →+* ZMod (p ^ n) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))

/--
**The coherence predicate.**

A sequence is coherent if xₙ₊₁ projects to xₙ.
-/
def IsCoherent (seq : (n : ℕ) → ZMod (p ^ n)) : Prop :=
  ∀ n, cast_down p n (seq (n + 1)) = seq n

/--
**The set of coherent sequences as a Subring.**
-/
def InverseLimitSubring : Subring ((n : ℕ) → ZMod (p ^ n)) where
  carrier := { seq | IsCoherent p seq }
  mul_mem' {a b} ha hb := by
    intro n
    dsimp [IsCoherent] at *
    -- cast_down is a RingHom, so it preserves mul
    rw [← map_mul (cast_down p n), ha n, hb n]
    rfl
  one_mem' := by
    intro n
    dsimp [IsCoherent]
    rw [← map_one (cast_down p n)]
    rfl
  add_mem' {a b} ha hb := by
    intro n
    dsimp [IsCoherent] at *
    rw [← map_add (cast_down p n), ha n, hb n]
    rfl
  zero_mem' := by
    intro n
    dsimp [IsCoherent]
    rw [← map_zero (cast_down p n)]
    rfl
  neg_mem' {a} ha := by
    intro n
    dsimp [IsCoherent] at *
    rw [← map_neg (cast_down p n), ha n]
    rfl

/-- The Inverse Limit Type. -/
abbrev InverseLimit := InverseLimitSubring p

instance : CommRing (InverseLimit p) := (InverseLimitSubring p).toCommRing

namespace InverseLimit

/-- The projection from the Inverse Limit to the n-th layer. -/
def project (n : ℕ) : InverseLimit p →+* ZMod (p ^ n) :=
  (Pi.evalRingHom (fun k => ZMod (p ^ k)) n).comp (InverseLimitSubring p).subtype

theorem coherent_trans (x : InverseLimit p) (m n : ℕ) (h : m ≤ n) :
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (x.val n) = x.val m := by
  induction n, h using Nat.le_induction with
  | base =>
    simp only [ZMod.castHom_self, RingHom.id_apply]
  | succ n hmn ih =>
    rw [← ih]
    have h_coh := x.property n
    dsimp [IsCoherent] at h_coh
    dsimp [cast_down] at h_coh
    rw [← h_coh]
    rw [ZMod.castHom_comp]

noncomputable section Isomorphism

/-- Map from ℤ_[p] to the Inverse Limit. -/
def toInverseLimit : ℤ_[p] →+* InverseLimit p where
  toFun x := ⟨fun n => PadicInt.toZModPow n x, fun n => by
    dsimp [IsCoherent, cast_down]
    simp only [PadicInt.cast_toZModPow, Nat.le_succ]⟩
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Map from the Inverse Limit to ℤ_[p]. -/
def fromInverseLimit : InverseLimit p →+* ℤ_[p] :=
  PadicInt.lift (f := fun n => project p n) <| by
    intro k1 k2 h
    ext x
    dsimp [project]
    rw [coherent_trans _ _ _ _ _ h]

/--
**Theorem: The One Ring Isomorphism.**
-/
def padic_is_inverse_limit : ℤ_[p] ≃+* InverseLimit p where
  toFun := toInverseLimit p
  invFun := fromInverseLimit p
  left_inv x := by
    dsimp [toInverseLimit, fromInverseLimit]
    refine (PadicInt.lift_unique (f := fun n => project p n) _ (id : ℤ_[p] →+* ℤ_[p]) ?_).symm
    intro n
    ext x
    simp [project]
  right_inv x := by
    dsimp [toInverseLimit, fromInverseLimit]
    apply Subtype.val_injective
    funext n
    dsimp [project]
    rw [PadicInt.lift_spec]
    rfl

end Isomorphism

end InverseLimit

end InverseLimit
