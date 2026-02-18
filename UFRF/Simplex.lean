import Mathlib.Data.Nat.Choose.Basic

/-!
# UFRF.Simplex

**Simplicial Topology: Boundary Face Counting**

The number 4 (the Log3 duality factor) is derived from combinatorial
topology. A 3-simplex (tetrahedron) — the fundamental object in the
Trinity's 3-dimensional embedding space — has exactly 4 boundary 2-faces.

This is a theorem of combinatorial topology:
  An n-simplex has C(n+1, n) = n+1 boundary (n-1)-faces.
  For n=3: C(4,3) = 4.

The boundary operator ∂₃ on the standard 3-simplex [a,b,c,d] produces:
  ∂₃[a,b,c,d] = [b,c,d] − [a,c,d] + [a,b,d] − [a,b,c]

That is exactly **4** oriented 2-faces. This is provable, not axiomatic.

## Connection to UFRF

The 3-simplex lives naturally in the EmbeddingDimension (3) + 1 vertex
space. Its 4 boundary faces correspond to the duality factor of the
Log3 (Cubed) tensor grade, which produces the coefficient 4 in the
fine structure polynomial: 4π³ + π² + π.

## References
- Stanford CS164: Simplicial Homology (graphics.stanford.edu)
- Mathlib: `Nat.choose`
-/

/--
**Theorem: A 3-simplex has exactly 4 boundary 2-faces.**

C(4,3) = 4. This is the number of ways to choose 3 vertices
from 4 (i.e., the number of triangular faces of a tetrahedron).

✅ PROVEN
-/
theorem simplex3_face_count : Nat.choose 4 3 = 4 := by decide

/--
The boundary face count of the standard 3-simplex.
This replaces the former `merkaba_geometric_factor` axiom.
-/
def simplex3_boundary_face_count : ℕ := Nat.choose 4 3

/--
**Theorem: The boundary face count equals 4.**

✅ PROVEN
-/
theorem simplex3_boundary_is_four : simplex3_boundary_face_count = 4 := by
  unfold simplex3_boundary_face_count
  exact simplex3_face_count

/--
**Generalization: An n-simplex has (n+1) boundary (n-1)-faces.**

For any n ≥ 1, C(n+1, n) = n+1.

✅ PROVEN
-/
theorem simplex_face_count_general (n : ℕ) :
    Nat.choose (n + 1) n = n + 1 := by
  rw [Nat.choose_succ_self_right]
