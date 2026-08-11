import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoConormalBasis
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoGradedAlgebra
import Mathlib.Algebra.Module.GradedModule

/-!
# The graded conormal generators of the N25 binary complete intersection

The canonical cone is cut out by a quadric `Q` and a cubic `C`.  The
ungraded conormal equivalence identifies `I/I²` with `(S/I)²`; this file
records the grading hidden by that equivalence.  A coefficient of the
quadric has degree shifted by two, while a coefficient of the cubic has
degree shifted by three.  Their images therefore define the literal degree
pieces of the conormal module.

The construction proves two facts needed by adjunction.  First, multiplication
by a homogeneous quotient class adds degrees.  Second, the distinguished
classes of `Q` and `C` occur in degrees two and three respectively.  This is
the module-theoretic content of the expected graded formula
`I/I² ≅ (S/I)(-2) ⊕ (S/I)(-3)` before the remaining internal-direct-sum and
sheafification layers are installed.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoConormalGrading

open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoConormalBasis
open RationalPointsN25QuotientTwoQuotientGrading

/-- The characteristic-two ground field of the canonical cone. -/
abbrev k := ZMod 2

/-! ## Shifted coefficient pieces -/

/-- The coefficient piece for a generator of degree `debt`.

In total degree `n`, such a coefficient must have quotient degree
`n - debt`; degrees below `debt` contain no coefficient and are represented
by the bottom submodule. -/
def shiftedLiteralPiece (debt n : ℕ) : Submodule k B :=
  if debt ≤ n then literalConePiece (n - debt) else ⊥

/-- The degree-`n` coefficient pairs for the quadric and cubic generators.

The first coordinate is shifted by two and the second by three, reflecting
the degrees of the two equations of the complete intersection. -/
def conormalCoefficientPiece (n : ℕ) : Submodule k (B × B) :=
  (shiftedLiteralPiece 2 n).prod (shiftedLiteralPiece 3 n)

/-! ## Scalar compatibility and the transported pieces -/

/-- The `k`-action on `I/I²` agrees with the action obtained by first mapping
`k` into `B = S/I`.

Mathlib supplies these two module structures through different quotient
constructions, so their equality is not definitional.  Lifting an element to
`I`, applying the quotient-scalar formula, and then using the scalar tower
through `S` proves the compatibility without adding a new global instance. -/
theorem algebraMap_smul_conormal (c : k) (m : I.Cotangent) :
    algebraMap k B c • m = c • m := by
  rcases I.toCotangent_surjective m with ⟨p, rfl⟩
  change Ideal.Quotient.mk I (algebraMap k R c) • I.toCotangent p = _
  rw [quotient_smul_toCotangent, I.toCotangent.map_smul]
  exact IsScalarTower.algebraMap_smul R c (I.toCotangent p)

/-- The conormal equivalence regarded as a `k`-linear map.

This restricted-scalar form is used to transport the shifted coefficient
submodules into `I/I²`. -/
def conormalLinearMapK : B × B →ₗ[k] I.Cotangent where
  toFun := conormalLinearEquiv
  map_add' := conormalLinearEquiv.map_add
  map_smul' c x := by
    calc
      conormalLinearEquiv (c • x) =
          conormalLinearEquiv (algebraMap k B c • x) := by
            apply congrArg conormalLinearEquiv
            ext <;> exact (IsScalarTower.algebraMap_smul B c _).symm
      _ = algebraMap k B c • conormalLinearEquiv x :=
        conormalLinearEquiv.map_smul (algebraMap k B c) x
      _ = c • conormalLinearEquiv x :=
        algebraMap_smul_conormal c (conormalLinearEquiv x)

/-- The degree-`n` conormal piece, obtained by transporting coefficient pairs
of shifted degrees `n-2` and `n-3` through the conormal equivalence. -/
def conormalPiece (n : ℕ) : Submodule k I.Cotangent :=
  (conormalCoefficientPiece n).map conormalLinearMapK

/-- Membership in a conormal degree piece is exactly the existence of a
quadric coefficient of degree `n-2` and a cubic coefficient of degree `n-3`
representing the class. -/
theorem mem_conormalPiece_iff {n : ℕ} {x : I.Cotangent} :
    x ∈ conormalPiece n ↔
      ∃ a ∈ shiftedLiteralPiece 2 n,
        ∃ b ∈ shiftedLiteralPiece 3 n,
          conormalLinearEquiv (a, b) = x := by
  rw [conormalPiece, Submodule.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨a, hab.1, b, hab.2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-! ## Homogeneous multiplication and generator degrees -/

/-- Multiplication by a quotient class of degree `i` sends the conormal
degree-`j` piece into degree `i+j`.

The proof works on the two coefficients separately and uses the established
graded multiplication in `B`.  If a requested shifted degree lies below its
generator degree, its coefficient is zero and remains zero after
multiplication. -/
theorem smul_mem_conormalPiece {i j : ℕ} {r : B} {m : I.Cotangent}
    (hr : r ∈ literalConePiece i) (hm : m ∈ conormalPiece j) :
    r • m ∈ conormalPiece (i + j) := by
  rw [mem_conormalPiece_iff] at hm ⊢
  rcases hm with ⟨a, ha, b, hb, rfl⟩
  refine ⟨r * a, ?_, r * b, ?_, ?_⟩
  · by_cases hj : 2 ≤ j
    · rw [shiftedLiteralPiece, if_pos hj] at ha
      rw [shiftedLiteralPiece, if_pos (le_add_of_le_right hj)]
      have hdeg : i + (j - 2) = i + j - 2 := by omega
      rw [← hdeg]
      exact mul_mem_literalConePiece hr ha
    · rw [shiftedLiteralPiece, if_neg hj, Submodule.mem_bot] at ha
      rw [ha, mul_zero]
      exact Submodule.zero_mem _
  · by_cases hj : 3 ≤ j
    · rw [shiftedLiteralPiece, if_pos hj] at hb
      rw [shiftedLiteralPiece, if_pos (le_add_of_le_right hj)]
      have hdeg : i + (j - 3) = i + j - 3 := by omega
      rw [← hdeg]
      exact mul_mem_literalConePiece hr hb
    · rw [shiftedLiteralPiece, if_neg hj, Submodule.mem_bot] at hb
      rw [hb, mul_zero]
      exact Submodule.zero_mem _
  · simpa [smul_eq_mul] using conormalLinearEquiv.map_smul r (a, b)

/-- The class of the defining quadric is homogeneous of conormal degree two. -/
theorem quadricClass_mem_conormalPiece :
    quadricClass ∈ conormalPiece 2 := by
  rw [mem_conormalPiece_iff]
  refine ⟨1, ?_, 0, ?_, ?_⟩
  · simpa [shiftedLiteralPiece] using one_mem_literalConePiece
  · simp [shiftedLiteralPiece]
  · change conormalGenerators (1, 0) = quadricClass
    rw [conormalGenerators_apply]
    have hzero : (0 : B) • cubicClass = 0 := zero_smul B cubicClass
    have hone : (1 : B) • quadricClass = quadricClass := one_smul B quadricClass
    rw [hzero, hone, add_zero]

/-- The class of the defining cubic is homogeneous of conormal degree three. -/
theorem cubicClass_mem_conormalPiece :
    cubicClass ∈ conormalPiece 3 := by
  rw [mem_conormalPiece_iff]
  refine ⟨0, ?_, 1, ?_, ?_⟩
  · simp [shiftedLiteralPiece]
  · simpa [shiftedLiteralPiece] using one_mem_literalConePiece
  · change conormalGenerators (0, 1) = cubicClass
    rw [conormalGenerators_apply]
    have hzero : (0 : B) • quadricClass = 0 := zero_smul B quadricClass
    have hone : (1 : B) • cubicClass = cubicClass := one_smul B cubicClass
    rw [hzero, hone, zero_add]

/-- The literal quotient grading acts homogeneously on the transported
conormal degree pieces. -/
noncomputable instance conormalPiece_gradedSMul :
    SetLike.GradedSMul literalConePiece conormalPiece where
  smul_mem := fun _ _ _ _ hr hm ↦ smul_mem_conormalPiece hr hm

end MazurProof.RationalPointsN25QuotientTwoConormalGrading
