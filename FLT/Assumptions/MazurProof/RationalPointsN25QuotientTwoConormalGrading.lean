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

The construction proves the three module-theoretic facts needed by
adjunction.  Multiplication by a homogeneous quotient class adds degrees,
the distinguished classes of `Q` and `C` occur in degrees two and three,
and the transported degree pieces form an internal direct sum.  Thus the
expected graded formula `I/I² ≅ (S/I)(-2) ⊕ (S/I)(-3)` is explicit before
the remaining sheafification layer is installed.
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

/-! ## Internal directness of the shifted pieces -/

/-- A quotient class of degree `d` is the same vector when regarded as a
coefficient of total degree `debt+d` for a generator of degree `debt`. -/
def literalToShifted (debt d : ℕ) :
    literalConePiece d ≃ₗ[k] shiftedLiteralPiece debt (debt + d) :=
  LinearEquiv.ofEq _ _ (by simp [shiftedLiteralPiece])

/-- The direct sum of all coefficient pieces shifted by `debt`. -/
abbrev ShiftedDirectSum (debt : ℕ) :=
  DirectSum ℕ (fun n ↦ shiftedLiteralPiece debt n)

/-- The direct sum of the literal homogeneous pieces of `B`. -/
abbrev LiteralDirectSum :=
  DirectSum ℕ (fun d ↦ literalConePiece d)

/-- Reindex a finitely supported homogeneous decomposition by adding
`debt` to every degree. -/
def shiftLiteralDirectSum (debt : ℕ) :
    LiteralDirectSum →ₗ[k] ShiftedDirectSum debt :=
  DirectSum.toModule k ℕ (ShiftedDirectSum debt)
    (fun d ↦ (DirectSum.lof k ℕ (fun n ↦ shiftedLiteralPiece debt n) (debt + d)).comp
      (literalToShifted debt d).toLinearMap)

/-- Decompose a quotient class into coefficient pieces whose total degrees
are shifted upward by `debt`. -/
def shiftedDecompose (debt : ℕ) :
    B →ₗ[k] ShiftedDirectSum debt :=
  shiftLiteralDirectSum debt ∘ₗ DirectSum.decomposeLinearEquiv literalConePiece

/-- Recombining the shifted homogeneous decomposition recovers the original
quotient class. -/
theorem coe_shiftedDecompose (debt : ℕ) :
    DirectSum.coeLinearMap (shiftedLiteralPiece debt) ∘ₗ shiftedDecompose debt =
      LinearMap.id := by
  apply DirectSum.decompose_lhom_ext literalConePiece
  intro d
  ext x
  simp [shiftedDecompose, shiftLiteralDirectSum, literalToShifted]

/-- Decomposing a finitely supported family of shifted pieces recovers that
family, including the zero pieces below the shift. -/
theorem shiftedDecompose_coe (debt : ℕ) :
    shiftedDecompose debt ∘ₗ DirectSum.coeLinearMap (shiftedLiteralPiece debt) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    DirectSum.coeLinearMap_lof]
  by_cases hn : debt ≤ n
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hxlit : (x : B) ∈ literalConePiece d := by
      simpa [shiftedLiteralPiece] using x.property
    let y : literalConePiece d := ⟨x, hxlit⟩
    change shiftLiteralDirectSum debt
        (DirectSum.decomposeLinearEquiv literalConePiece (x : B)) =
      DirectSum.lof k ℕ (fun i ↦ shiftedLiteralPiece debt i) (debt + d) x
    rw [show (x : B) = (y : B) by rfl,
      DirectSum.decomposeLinearEquiv_apply_coe]
    simp only [shiftLiteralDirectSum, DirectSum.toModule_lof,
      LinearMap.comp_apply]
    apply congrArg
    apply Subtype.ext
    rfl
  · have hx : x = 0 := by
      apply Subtype.ext
      simpa [shiftedLiteralPiece, hn] using x.property
    subst x
    simp

/-- Shifting homogeneous indices does not change the underlying quotient
module: `B` is linearly equivalent to the direct sum of its shifted pieces. -/
def shiftedLinearEquiv (debt : ℕ) :
    B ≃ₗ[k] ShiftedDirectSum debt :=
  { shiftedDecompose debt with
    invFun := DirectSum.coeLinearMap (shiftedLiteralPiece debt)
    left_inv := fun x ↦ LinearMap.congr_fun (coe_shiftedDecompose debt) x
    right_inv := fun x ↦ LinearMap.congr_fun (shiftedDecompose_coe debt) x }

/-! ## Combining the two equation shifts -/

/-- The direct sum whose `n`th component is the product of the two shifted
coefficient pieces. -/
abbrev PairedShiftedDirectSum :=
  DirectSum ℕ (fun n ↦ shiftedLiteralPiece 2 n × shiftedLiteralPiece 3 n)

/-- Zip two finitely supported families componentwise.

Its inverse takes the first and second projections.  Finite support is
preserved because the support of the zipped family is contained in the union
of the two original supports. -/
def zipShiftedDirectSums :
    (ShiftedDirectSum 2 × ShiftedDirectSum 3) ≃ₗ[k] PairedShiftedDirectSum where
  toFun x := DFinsupp.zipWith (fun _ a b ↦ (a, b)) (fun _ ↦ rfl) x.1 x.2
  invFun x :=
    (DirectSum.lmap (fun n ↦ LinearMap.fst k
      (shiftedLiteralPiece 2 n) (shiftedLiteralPiece 3 n)) x,
     DirectSum.lmap (fun n ↦ LinearMap.snd k
      (shiftedLiteralPiece 2 n) (shiftedLiteralPiece 3 n)) x)
  map_add' x y := by
    ext n <;> simp [DFinsupp.zipWith_apply]
  map_smul' c x := by
    ext n <;> rfl
  left_inv x := by
    ext n <;> simp [DFinsupp.zipWith_apply]
  right_inv x := by
    ext n <;> simp [DFinsupp.zipWith_apply]

/-- Unzipping a family supported in one degree preserves that support and
projects the coefficient pair in that degree. -/
theorem zipShiftedDirectSums_symm_lof (n : ℕ)
    (x : shiftedLiteralPiece 2 n × shiftedLiteralPiece 3 n) :
    zipShiftedDirectSums.symm
        (DirectSum.lof k ℕ
          (fun i ↦ shiftedLiteralPiece 2 i × shiftedLiteralPiece 3 i) n x) =
      (DirectSum.lof k ℕ (fun i ↦ shiftedLiteralPiece 2 i) n x.1,
       DirectSum.lof k ℕ (fun i ↦ shiftedLiteralPiece 3 i) n x.2) := by
  change
    (DirectSum.lmap (fun i ↦ LinearMap.fst k
        (shiftedLiteralPiece 2 i) (shiftedLiteralPiece 3 i))
        (DirectSum.lof k ℕ
          (fun i ↦ shiftedLiteralPiece 2 i × shiftedLiteralPiece 3 i) n x),
     DirectSum.lmap (fun i ↦ LinearMap.snd k
        (shiftedLiteralPiece 2 i) (shiftedLiteralPiece 3 i))
        (DirectSum.lof k ℕ
          (fun i ↦ shiftedLiteralPiece 2 i × shiftedLiteralPiece 3 i) n x)) = _
  rw [DirectSum.lmap_lof, DirectSum.lmap_lof]
  exact Prod.ext rfl rfl

/-- A pair of elements in the two shifted submodules is canonically the same
as an element of their product submodule in `B × B`. -/
def coefficientComponentEquiv (n : ℕ) :
    (shiftedLiteralPiece 2 n × shiftedLiteralPiece 3 n) ≃ₗ[k]
      conormalCoefficientPiece n where
  toFun x := ⟨(x.1, x.2), x.1.property, x.2.property⟩
  invFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The direct sum of all shifted quadric-cubic coefficient-pair pieces. -/
abbrev CoefficientDirectSum :=
  DirectSum ℕ (fun n ↦ conormalCoefficientPiece n)

/-- The coefficient module `(B × B)` decomposes as the internal direct sum
of the degreewise pairs `B_{n-2} × B_{n-3}`. -/
def coefficientDecomposeEquiv :
    (B × B) ≃ₗ[k] CoefficientDirectSum :=
  ((shiftedLinearEquiv 2).prodCongr (shiftedLinearEquiv 3)).trans
    (zipShiftedDirectSums.trans
      (DirectSum.congrLinearEquiv coefficientComponentEquiv))

/-- The inverse of the coefficient decomposition is literal recomposition in
`B × B`. -/
theorem coefficientDecomposeEquiv_symm :
    coefficientDecomposeEquiv.symm.toLinearMap =
      DirectSum.coeLinearMap conormalCoefficientPiece := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  change ((shiftedLinearEquiv 2).prodCongr (shiftedLinearEquiv 3)).symm
      (zipShiftedDirectSums.symm
        ((DirectSum.congrLinearEquiv coefficientComponentEquiv).symm
          (DirectSum.lof k ℕ (fun i ↦ conormalCoefficientPiece i) n x))) = x.1
  rw [show (DirectSum.congrLinearEquiv coefficientComponentEquiv).symm
      (DirectSum.lof k ℕ (fun i ↦ conormalCoefficientPiece i) n x) =
        DirectSum.lof k ℕ
          (fun i ↦ shiftedLiteralPiece 2 i × shiftedLiteralPiece 3 i) n
          ((coefficientComponentEquiv n).symm x) by
        change DirectSum.lmap
            (fun i ↦ (coefficientComponentEquiv i).symm.toLinearMap)
            (DirectSum.lof k ℕ (fun i ↦ conormalCoefficientPiece i) n x) = _
        rw [DirectSum.lmap_lof]
        rfl]
  rw [zipShiftedDirectSums_symm_lof]
  rw [LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
  change
    (DirectSum.coeLinearMap (shiftedLiteralPiece 2)
        (DirectSum.lof k ℕ (fun i ↦ shiftedLiteralPiece 2 i) n
          ⟨(x : B × B).1, x.2.1⟩),
      DirectSum.coeLinearMap (shiftedLiteralPiece 3)
        (DirectSum.lof k ℕ (fun i ↦ shiftedLiteralPiece 3 i) n
          ⟨(x : B × B).2, x.2.2⟩)) = x.1
  simp only [DirectSum.coeLinearMap_lof]

/-- The shifted coefficient-pair pieces form an internal direct sum. -/
theorem conormalCoefficientPiece_isInternal :
    DirectSum.IsInternal conormalCoefficientPiece := by
  change Function.Bijective (DirectSum.coeLinearMap conormalCoefficientPiece)
  rw [← coefficientDecomposeEquiv_symm]
  exact coefficientDecomposeEquiv.symm.bijective

/-! ## Transport to the conormal module -/

/-- The restricted-scalar conormal generator map is bijective because its
underlying function is the already-proved conormal equivalence. -/
theorem conormalLinearMapK_bijective :
    Function.Bijective conormalLinearMapK := by
  constructor
  · exact conormalLinearEquiv.injective
  · exact conormalLinearEquiv.surjective

/-- The conormal equivalence as an actual `k`-linear equivalence. -/
def conormalLinearEquivK : (B × B) ≃ₗ[k] I.Cotangent :=
  LinearEquiv.ofBijective conormalLinearMapK conormalLinearMapK_bijective

/-- In each degree, the conormal equivalence restricts to an equivalence from
the shifted coefficient pair onto the transported conormal piece. -/
def coefficientToConormalPiece (n : ℕ) :
    conormalCoefficientPiece n ≃ₗ[k] conormalPiece n :=
  conormalLinearEquivK.ofSubmodules _ _ (by
    change (conormalCoefficientPiece n).map conormalLinearMapK = _
    rfl)

/-- The direct sum of the transported conormal degree pieces. -/
abbrev ConormalDirectSum := DirectSum ℕ (fun n ↦ conormalPiece n)

/-- The explicit graded decomposition of `I/I²`.

It first returns to coefficient pairs, decomposes the two coordinates with
shifts two and three, and finally transports each component back to the
conormal module. -/
def conormalDecomposeEquiv :
    I.Cotangent ≃ₗ[k] ConormalDirectSum :=
  conormalLinearEquivK.symm.trans <|
    coefficientDecomposeEquiv.trans <|
      DirectSum.congrLinearEquiv coefficientToConormalPiece

/-- The inverse of the explicit conormal decomposition is the canonical sum
of the included conormal pieces. -/
theorem conormalDecomposeEquiv_symm :
    conormalDecomposeEquiv.symm.toLinearMap =
      DirectSum.coeLinearMap conormalPiece := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
  change conormalDecomposeEquiv.symm
      (DirectSum.lof k ℕ (fun i ↦ conormalPiece i) n x) = x
  change conormalLinearEquivK
      (coefficientDecomposeEquiv.symm
        ((DirectSum.congrLinearEquiv coefficientToConormalPiece).symm
          (DirectSum.lof k ℕ (fun i ↦ conormalPiece i) n x))) = x
  rw [show (DirectSum.congrLinearEquiv coefficientToConormalPiece).symm
      (DirectSum.lof k ℕ (fun i ↦ conormalPiece i) n x) =
        DirectSum.lof k ℕ (fun i ↦ conormalCoefficientPiece i) n
          ((coefficientToConormalPiece n).symm x) by
        change DirectSum.lmap
            (fun i ↦ (coefficientToConormalPiece i).symm.toLinearMap)
            (DirectSum.lof k ℕ (fun i ↦ conormalPiece i) n x) = _
        rw [DirectSum.lmap_lof]
        rfl]
  rw [show coefficientDecomposeEquiv.symm
      (DirectSum.lof k ℕ (fun i ↦ conormalCoefficientPiece i) n
        ((coefficientToConormalPiece n).symm x)) =
      ((coefficientToConormalPiece n).symm x : B × B) by
        have h := LinearMap.congr_fun coefficientDecomposeEquiv_symm
          (DirectSum.lof k ℕ (fun i ↦ conormalCoefficientPiece i) n
            ((coefficientToConormalPiece n).symm x))
        simpa using h]
  exact congrArg Subtype.val ((coefficientToConormalPiece n).apply_symm_apply x)

/-- The transported conormal degree pieces form an internal direct sum in
`I/I²`. -/
theorem conormalPiece_isInternal :
    DirectSum.IsInternal conormalPiece := by
  change Function.Bijective (DirectSum.coeLinearMap conormalPiece)
  rw [← conormalDecomposeEquiv_symm]
  exact conormalDecomposeEquiv.symm.bijective

/-- The literal quotient grading acts homogeneously on the transported
conormal degree pieces. -/
noncomputable instance conormalPiece_gradedSMul :
    SetLike.GradedSMul literalConePiece conormalPiece where
  smul_mem := fun _ _ _ _ hr hm ↦ smul_mem_conormalPiece hr hm

/-- The explicit conormal equivalence supplies canonical decomposition and
recomposition maps for the internal grading. -/
noncomputable instance conormalPiece_decomposition :
    DirectSum.Decomposition conormalPiece where
  decompose' := conormalDecomposeEquiv
  left_inv x := by
    change DirectSum.coeLinearMap conormalPiece (conormalDecomposeEquiv x) = x
    rw [← conormalDecomposeEquiv_symm]
    exact conormalDecomposeEquiv.symm_apply_apply x
  right_inv x := by
    change conormalDecomposeEquiv (DirectSum.coeLinearMap conormalPiece x) = x
    rw [← conormalDecomposeEquiv_symm]
    exact conormalDecomposeEquiv.apply_symm_apply x

end MazurProof.RationalPointsN25QuotientTwoConormalGrading
