import FLT.Assumptions.MazurProof.CurveZetaFrobeniusOrbitGrading
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientExtensionPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientThreeBaseChange
import Mathlib.FieldTheory.Finite.Extension

/-!
# Frobenius orbits for the characteristic-three N25 curve

All four finite fields used by the N25 point count embed in the common field
`𝔽_(3^12)`.  Arithmetic Frobenius on the canonical curve over that field
has the following fixed-point interpretation:

* its `d`-th iterate fixes exactly the coordinates in `𝔽_(3^d)` for
  `d ∈ {1,2,3,4}`;
* normalized projective charts descend coordinate by coordinate, because the
  canonical quadric and cubic are defined over `𝔽₃`;
* hence field-valued curve points are exactly fixed points of the corresponding
  Frobenius iterate.

The general permutation-orbit theorem then turns those fixed points into a
locally finite grading that is complete through degree four.  Arithmetic
Frobenius is the inverse of the geometric convention often used for closed
points; inverse generators have the same cyclic orbits and exact periods, so
the choice changes only the orientation of the position coordinate.  This is
a structural Galois-orbit proof, not a comparison of the four already known
point cardinalities.
-/

namespace MazurProof.RationalPointsN25QuotientFrobeniusOrbits

open Polynomial
open CurveZetaFrobeniusOrbitGrading
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientWeilThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmallThreeSemantic
open RationalPointsN25QuotientThreeBaseChange
open RationalPointsN25QuotientMiddleRiemannRoch

/-! ## A common finite field and its distinguished subfields -/

/-- The field `𝔽_(3^12)` contains the extensions of degrees one through
four because each of those degrees divides twelve. -/
abbrev CommonThreeField := GaloisField 3 12

/-- The finite type on the common field is chosen from its canonical
finiteness instance. -/
noncomputable instance commonThreeFieldFintype : Fintype CommonThreeField :=
  Fintype.ofFinite CommonThreeField

/-- Embed the canonical degree-`d` Galois field in the common degree-twelve
field.  Divisibility of extension degrees is exactly the finite-field
subfield criterion. -/
noncomputable def galoisFieldToCommon
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12) :
    GaloisField 3 d →ₐ[ZMod 3] CommonThreeField :=
  (FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 3) (K := GaloisField 3 d) (L := CommonThreeField) (by
      rw [GaloisField.finrank 3 hdpos.ne',
        GaloisField.finrank 3 (by decide : 12 ≠ 0)]
      exact hd)).some

/-- Embed any finite characteristic-three field of cardinality `3^d` into
the common field.  The public map is a ring homomorphism so its type does not
carry a second, potentially conflicting algebra structure on the source. -/
noncomputable def finiteFieldToCommon
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) : K →+* CommonThreeField := by
  letI : Algebra (ZMod 3) K := ZMod.algebra K 3
  exact ((galoisFieldToCommon d hdpos hd).comp
    (GaloisField.algEquivGaloisFieldOfFintype 3 d hcard).toAlgHom).toRingHom

/-! ## The fixed subfield of an iterate of Frobenius -/

/-- The roots in the common field of `X^(3^d)-X`, written as a subtype.
They will be identified with every embedded field of cardinality `3^d`. -/
def PowerFixed (d : ℕ) :=
  {x : CommonThreeField // x ^ (3 ^ d) = x}

/-- The Frobenius-fixed subtype is finite because it injects into the common
finite field. -/
noncomputable instance powerFixedFintype (d : ℕ) : Fintype (PowerFixed d) :=
  have : Finite (PowerFixed d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  Fintype.ofFinite (PowerFixed d)

/-- The finite-field embedding lands in the `3^d`-power fixed subfield by
the universal identity `a^(#K)=a` in a finite field. -/
noncomputable def finiteFieldToPowerFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) : K → PowerFixed d := by
  intro a
  refine ⟨finiteFieldToCommon K d hdpos hd hcard a, ?_⟩
  rw [← hcard, ← map_pow]
  exact congrArg (finiteFieldToCommon K d hdpos hd hcard)
    (FiniteField.pow_card a)

/-- The map into the power-fixed subtype is injective because its underlying
field homomorphism is injective. -/
theorem finiteFieldToPowerFixed_injective
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) :
    Function.Injective
      (finiteFieldToPowerFixed K d hdpos hd hcard) := by
  intro a b hab
  apply (finiteFieldToCommon K d hdpos hd hcard).injective
  exact congrArg Subtype.val hab

/-- A positive power of three is strictly larger than one. -/
theorem three_pow_ne_one (d : ℕ) (hd : 0 < d) : 3 ^ d ≠ 1 := by
  exact ne_of_gt (one_lt_pow₀ (by omega) hd.ne')

/-- For positive `d`, the polynomial `X^(3^d)-X` has degree `3^d`; the
linear term cannot cancel its leading monomial. -/
theorem commonPolynomial_natDegree (d : ℕ) (hd : 0 < d) :
    (X ^ (3 ^ d) - X : CommonThreeField[X]).natDegree = 3 ^ d := by
  calc
    (X ^ (3 ^ d) - X : CommonThreeField[X]).natDegree =
        (X ^ (3 ^ d) : CommonThreeField[X]).natDegree :=
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
        rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
        exact one_lt_pow₀ (by omega) hd.ne')
    _ = 3 ^ d :=
      Polynomial.natDegree_X_pow (R := CommonThreeField) (3 ^ d)

/-- The fixed-subfield polynomial is nonzero in every positive degree, as
its computed degree is positive. -/
theorem commonPolynomial_ne_zero (d : ℕ) (hd : 0 < d) :
    (X ^ (3 ^ d) - X : CommonThreeField[X]) ≠ 0 := by
  intro hzero
  have hdegree := congrArg Polynomial.natDegree hzero
  rw [commonPolynomial_natDegree d hd, Polynomial.natDegree_zero] at hdegree
  exact (pow_pos (by norm_num : (0 : ℕ) < 3) d).ne' hdegree

/-- A power-fixed element is a root of `X^(3^d)-X`.  This embedding lets the
polynomial root bound control the size of the fixed subfield. -/
noncomputable def powerFixedToRootSet (d : ℕ) (hd : 0 < d) :
    PowerFixed d ↪ (X ^ (3 ^ d) - X : CommonThreeField[X]).rootSet
      CommonThreeField where
  toFun x := ⟨x.1, by
    rw [Polynomial.mem_rootSet]
    refine ⟨commonPolynomial_ne_zero d hd, ?_⟩
    simpa [Polynomial.aeval_def] using sub_eq_zero.mpr x.2⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg
      (fun z : (X ^ (3 ^ d) - X : CommonThreeField[X]).rootSet
        CommonThreeField => z.1) h

/-- The fixed subfield has at most `3^d` elements by the root bound for
`X^(3^d)-X`. -/
theorem powerFixed_card_le (d : ℕ) (hd : 0 < d) :
    Fintype.card (PowerFixed d) ≤ 3 ^ d := by
  letI : Fintype
      ((X ^ (3 ^ d) - X : CommonThreeField[X]).rootSet CommonThreeField) :=
    Fintype.ofFinite _
  calc
    Fintype.card (PowerFixed d) ≤
        Fintype.card
          ((X ^ (3 ^ d) - X : CommonThreeField[X]).rootSet CommonThreeField) :=
      Fintype.card_le_of_injective _ (powerFixedToRootSet d hd).injective
    _ = Set.ncard
          ((X ^ (3 ^ d) - X : CommonThreeField[X]).rootSet CommonThreeField) := by
      exact Set.fintypeCard_eq_ncard
        ((X ^ (3 ^ d) - X : CommonThreeField[X]).rootSet CommonThreeField)
    _ ≤ (X ^ (3 ^ d) - X : CommonThreeField[X]).natDegree :=
      Polynomial.ncard_rootSet_le _ _
    _ = 3 ^ d := commonPolynomial_natDegree d hd

/-- The embedded field of cardinality `3^d` exhausts the power-fixed
subfield.  Injectivity gives the lower bound and the polynomial root bound
gives the matching upper bound. -/
noncomputable def finiteFieldEquivPowerFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) : K ≃ PowerFixed d := by
  let f := finiteFieldToPowerFixed K d hdpos hd hcard
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨finiteFieldToPowerFixed_injective K d hdpos hd hcard, ?_⟩
  apply Nat.le_antisymm
  · exact Fintype.card_le_of_injective f
      (finiteFieldToPowerFixed_injective K d hdpos hd hcard)
  · exact (powerFixed_card_le d hdpos).trans_eq hcard.symm

/-- The fixed-subfield equivalence is induced by the chosen finite-field
embedding; it is not an arbitrary equivalence obtained from equal
cardinalities. -/
@[simp]
theorem finiteFieldEquivPowerFixed_apply_val
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (a : K) :
    (finiteFieldEquivPowerFixed K d hdpos hd hcard a).1 =
      finiteFieldToCommon K d hdpos hd hcard a := rfl

/-! ## Arithmetic Frobenius on the common curve -/

/-- Arithmetic Frobenius `x ↦ x³` on the common characteristic-three
field. -/
noncomputable def commonFrobenius :
    CommonThreeField ≃ₐ[ZMod 3] CommonThreeField :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 3) CommonThreeField

/-- The `d`-th iterate of arithmetic Frobenius is the `3^d`-power map. -/
theorem commonFrobenius_pow_apply (d : ℕ) (x : CommonThreeField) :
    (commonFrobenius ^ d) x = x ^ (3 ^ d) := by
  have h := congrFun
    (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate
      (ZMod 3) CommonThreeField d) x
  simpa [commonFrobenius, AlgEquiv.coe_pow, ZMod.card] using h

/-- Canonical curve points over a field are normalized projective points
satisfying the characteristic-three quadric and cubic. -/
abbrev CurvePoint (K : Type*) [Field K] :=
  {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P}

/-- The common-field curve-point type is finite because it is a subtype of
the finite normalized projective space. -/
noncomputable instance commonCurvePointFintype :
    Fintype (CurvePoint CommonThreeField) :=
  have : Finite (CurvePoint CommonThreeField) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  Fintype.ofFinite (CurvePoint CommonThreeField)

/-- Frobenius acts on canonical curve points by applying it to every free
normalized projective coordinate. -/
noncomputable def commonPointFrobenius :
    Equiv.Perm (CurvePoint CommonThreeField) :=
  canonicalPointEquiv commonFrobenius.toRingEquiv

/-- Applying one map before or after its `d`-fold iterate gives the same
`(d+1)`-fold iterate.  The lemma keeps the coordinatewise Frobenius induction
independent of the internal representation of `Function.iterate`. -/
theorem self_iterate_commute_apply {A : Type*}
    (f : A → A) (d : ℕ) (x : A) :
    f (f^[d] x) = f^[d] (f x) := by
  calc
    f (f^[d] x) = f^[1] (f^[d] x) := rfl
    _ = f^[1 + d] x := (Function.iterate_add_apply f 1 d x).symm
    _ = f^[d + 1] x := by rw [Nat.add_comm]
    _ = f^[d] (f^[1] x) := Function.iterate_add_apply f d 1 x
    _ = f^[d] (f x) := rfl

/-- Iterating point Frobenius applies the iterated field Frobenius to every
free chart coordinate.  The proof is uniform across the four normalized
projective charts. -/
theorem commonPointFrobenius_iterate_val
    (d : ℕ) (P : CurvePoint CommonThreeField) :
    (commonPointFrobenius^[d] P).1 =
      NormalizedProjective4.map
        (commonFrobenius ^ d).toRingEquiv.toRingHom P.1 := by
  induction d with
  | zero =>
      cases P with
      | mk P hP =>
        cases P <;> rfl
  | succ d ih =>
      rw [Function.iterate_succ_apply']
      change NormalizedProjective4.map commonFrobenius.toRingEquiv.toRingHom
        (commonPointFrobenius^[d] P).1 =
          NormalizedProjective4.map
            (commonFrobenius ^ (d + 1)).toRingEquiv.toRingHom P.1
      rw [ih]
      cases P.1 <;>
        simp [NormalizedProjective4.map, pow_succ,
          self_iterate_commute_apply]

/-- Normalized projective points whose coordinates are fixed by the `d`-th
iterate of Frobenius. -/
def ProjectiveFrobeniusFixed (d : ℕ) :=
  {P : NormalizedProjective4 CommonThreeField //
    NormalizedProjective4.map
      (commonFrobenius ^ d).toRingEquiv.toRingHom P = P}

/-- Every embedded element of a degree-`d` field is fixed by the `d`-th
iterate of Frobenius on the common field. -/
theorem finiteFieldToCommon_frobenius_fixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (a : K) :
    (commonFrobenius ^ d) (finiteFieldToCommon K d hdpos hd hcard a) =
      finiteFieldToCommon K d hdpos hd hcard a := by
  rw [commonFrobenius_pow_apply]
  exact (finiteFieldToPowerFixed K d hdpos hd hcard a).2

/-- A coordinate fixed by the `d`-th Frobenius iterate satisfies the
`3^d`-power equation used by `PowerFixed`. -/
theorem frobenius_fixed_to_power_fixed
    (d : ℕ) (x : CommonThreeField) (hx : (commonFrobenius ^ d) x = x) :
    x ^ (3 ^ d) = x := by
  rw [← commonFrobenius_pow_apply]
  exact hx

/-- Descending an embedded source element through the fixed-subfield
equivalence returns the original element. -/
theorem finiteFieldEquivPowerFixed_symm_embedding
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (a : K)
    (ha : finiteFieldToCommon K d hdpos hd hcard a ^ (3 ^ d) =
      finiteFieldToCommon K d hdpos hd hcard a) :
    (finiteFieldEquivPowerFixed K d hdpos hd hcard).symm
      ⟨finiteFieldToCommon K d hdpos hd hcard a, ha⟩ = a := by
  let E := finiteFieldEquivPowerFixed K d hdpos hd hcard
  apply E.injective
  rw [E.apply_symm_apply]
  apply Subtype.ext
  rfl

/-- Re-embedding an element descended from the power-fixed subtype recovers
its original common-field coordinate. -/
theorem finiteFieldToCommon_symm_powerFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (x : CommonThreeField)
    (hx : x ^ (3 ^ d) = x) :
    finiteFieldToCommon K d hdpos hd hcard
      ((finiteFieldEquivPowerFixed K d hdpos hd hcard).symm ⟨x, hx⟩) = x := by
  let E := finiteFieldEquivPowerFixed K d hdpos hd hcard
  have h := congrArg Subtype.val (E.apply_symm_apply ⟨x, hx⟩)
  exact h

/-! ## Descent of normalized projective points and curve points -/

/-- Normalized projective points over a degree-`d` field are equivalent to
the normalized common-field points fixed by the `d`-th Frobenius iterate.
The inverse descends each free coordinate in its existing chart, so no
projective rescaling or cardinality argument is hidden in the construction. -/
noncomputable def projectiveEquivFrobeniusFixed
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) :
    NormalizedProjective4 K ≃ ProjectiveFrobeniusFixed d where
  toFun P := by
    refine ⟨NormalizedProjective4.map
      (finiteFieldToCommon K d hdpos hd hcard) P, ?_⟩
    cases P <;>
      simp only [NormalizedProjective4.map,
        NormalizedProjective4.xChart.injEq,
        NormalizedProjective4.yChart.injEq,
        NormalizedProjective4.zChart.injEq]
    · exact ⟨finiteFieldToCommon_frobenius_fixed K d hdpos hd hcard _,
        finiteFieldToCommon_frobenius_fixed K d hdpos hd hcard _,
        finiteFieldToCommon_frobenius_fixed K d hdpos hd hcard _⟩
    · exact ⟨finiteFieldToCommon_frobenius_fixed K d hdpos hd hcard _,
        finiteFieldToCommon_frobenius_fixed K d hdpos hd hcard _⟩
    · exact finiteFieldToCommon_frobenius_fixed K d hdpos hd hcard _
  invFun P := by
    let E := finiteFieldEquivPowerFixed K d hdpos hd hcard
    rcases P with ⟨P, hP⟩
    cases P with
    | xChart y z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.xChart.injEq] at hP
        exact .xChart
          (E.symm ⟨y, frobenius_fixed_to_power_fixed d y hP.1⟩)
          (E.symm ⟨z, frobenius_fixed_to_power_fixed d z hP.2.1⟩)
          (E.symm ⟨w, frobenius_fixed_to_power_fixed d w hP.2.2⟩)
    | yChart z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.yChart.injEq] at hP
        exact .yChart
          (E.symm ⟨z, frobenius_fixed_to_power_fixed d z hP.1⟩)
          (E.symm ⟨w, frobenius_fixed_to_power_fixed d w hP.2⟩)
    | zChart w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.zChart.injEq] at hP
        exact .zChart
          (E.symm ⟨w, frobenius_fixed_to_power_fixed d w hP⟩)
    | wChart => exact .wChart
  left_inv P := by
    cases P <;> simp only [NormalizedProjective4.map,
      NormalizedProjective4.xChart.injEq,
      NormalizedProjective4.yChart.injEq,
      NormalizedProjective4.zChart.injEq]
    · exact ⟨finiteFieldEquivPowerFixed_symm_embedding K d hdpos hd hcard _ _,
        finiteFieldEquivPowerFixed_symm_embedding K d hdpos hd hcard _ _,
        finiteFieldEquivPowerFixed_symm_embedding K d hdpos hd hcard _ _⟩
    · exact ⟨finiteFieldEquivPowerFixed_symm_embedding K d hdpos hd hcard _ _,
        finiteFieldEquivPowerFixed_symm_embedding K d hdpos hd hcard _ _⟩
    · exact finiteFieldEquivPowerFixed_symm_embedding K d hdpos hd hcard _ _
  right_inv P := by
    apply Subtype.ext
    rcases P with ⟨P, hP⟩
    cases P with
    | xChart y z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.xChart.injEq] at hP ⊢
        exact ⟨finiteFieldToCommon_symm_powerFixed K d hdpos hd hcard _ _,
          finiteFieldToCommon_symm_powerFixed K d hdpos hd hcard _ _,
          finiteFieldToCommon_symm_powerFixed K d hdpos hd hcard _ _⟩
    | yChart z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.yChart.injEq] at hP ⊢
        exact ⟨finiteFieldToCommon_symm_powerFixed K d hdpos hd hcard _ _,
          finiteFieldToCommon_symm_powerFixed K d hdpos hd hcard _ _⟩
    | zChart w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.zChart.injEq] at hP ⊢
        exact finiteFieldToCommon_symm_powerFixed K d hdpos hd hcard _ _
    | wChart => rfl

/-- Restricting projective fixed-field descent to the canonical equations
identifies curve points over a degree-`d` field with common-field curve points
fixed by the `d`-th iterate of Frobenius.  Preservation and reflection of the
equations use their prime-field coefficients and injectivity of field maps. -/
noncomputable def curvePointEquivFixedByIterate
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) :
    CurvePoint K ≃ FixedByIterate commonPointFrobenius d where
  toFun P := by
    let R := projectiveEquivFrobeniusFixed K d hdpos hd hcard P.1
    let Q : CurvePoint CommonThreeField :=
      ⟨R.1, by
        rw [show R.1 = NormalizedProjective4.map
          (finiteFieldToCommon K d hdpos hd hcard) P.1 from rfl]
        exact (isCanonicalNormalizedThree_map_iff
          (finiteFieldToCommon K d hdpos hd hcard) P.1).2 P.2⟩
    refine ⟨Q, ?_⟩
    apply Subtype.ext
    rw [commonPointFrobenius_iterate_val]
    exact R.2
  invFun Q := by
    have hraw : NormalizedProjective4.map
        (commonFrobenius ^ d).toRingEquiv.toRingHom Q.1.1 = Q.1.1 := by
      have h := congrArg Subtype.val Q.2
      rw [commonPointFrobenius_iterate_val] at h
      exact h
    let R : ProjectiveFrobeniusFixed d := ⟨Q.1.1, hraw⟩
    let P := (projectiveEquivFrobeniusFixed K d hdpos hd hcard).symm R
    refine ⟨P, ?_⟩
    apply (isCanonicalNormalizedThree_map_iff
      (finiteFieldToCommon K d hdpos hd hcard) P).1
    have hR := congrArg Subtype.val
      ((projectiveEquivFrobeniusFixed K d hdpos hd hcard).apply_symm_apply R)
    rw [show NormalizedProjective4.map
      (finiteFieldToCommon K d hdpos hd hcard) P = R.1 from hR]
    exact Q.1.2
  left_inv P := by
    apply Subtype.ext
    let E := projectiveEquivFrobeniusFixed K d hdpos hd hcard
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    let E := projectiveEquivFrobeniusFixed K d hdpos hd hcard
    have hraw : NormalizedProjective4.map
        (commonFrobenius ^ d).toRingEquiv.toRingHom Q.1.1 = Q.1.1 := by
      have h := congrArg Subtype.val Q.2
      rw [commonPointFrobenius_iterate_val] at h
      exact h
    let R : ProjectiveFrobeniusFixed d := ⟨Q.1.1, hraw⟩
    simpa only [E, R] using congrArg Subtype.val (E.apply_symm_apply R)

/-- The curve-point equivalence maps a point by the same coordinatewise
coefficient embedding used to construct the fixed subfield. -/
@[simp]
theorem curvePointEquivFixedByIterate_apply_val
    (K : Type*) [Field K] [Fintype K] [CharP K 3]
    (d : ℕ) (hdpos : 0 < d) (hd : d ∣ 12)
    (hcard : Fintype.card K = 3 ^ d) (P : CurvePoint K) :
    ((curvePointEquivFixedByIterate K d hdpos hd hcard P).1).1 =
      NormalizedProjective4.map
        (finiteFieldToCommon K d hdpos hd hcard) P.1 := rfl

/-! ## The four extension fields and the resulting closed-point bridge -/

/-- The four semantic extension point types are the fixed points of the
first four selected Frobenius iterates.  The cardinality equalities used here
describe only the coefficient fields; no curve point count enters the proof. -/
noncomputable def extensionFixedPointRealization25Three :
    FixedPointRealizationOn commonPointFrobenius ExtensionIndex25Three
      ExtensionIndex25Three.exponent ExtensionIndex25Three.pointType where
  realize i := by
    cases i with
    | degreeOne =>
        exact curvePointEquivFixedByIterate Trit 1 (by norm_num) (by norm_num)
          (by norm_num [ternary_extension_cardinalities])
    | degreeTwo =>
        exact curvePointEquivFixedByIterate F9 2 (by norm_num) (by norm_num)
          (by norm_num [ternary_extension_cardinalities])
    | degreeThree =>
        exact curvePointEquivFixedByIterate F27 3 (by norm_num) (by norm_num)
          (by norm_num [ternary_extension_cardinalities])
    | degreeFour =>
        exact curvePointEquivFixedByIterate F81 4 (by norm_num) (by norm_num)
          (by norm_num [ternary_extension_cardinalities])
  exponent_pos i := by
    cases i <;> norm_num [ExtensionIndex25Three.exponent]

/-- The exact arithmetic-Frobenius orbits in `𝔽_(3^12)`, used as a closed-point
grading through degree four.  Every orbit of degree at most four is present
because `1,2,3,4` divide twelve; no claim is made that this finite common field
contains the curve's closed points of all higher degrees. -/
noncomputable def frobeniusOrbitGrading25ThreeLE4 :=
  orbitClosedPointGrading commonPointFrobenius

/-- The concrete closed-point classification through degree four.  It sends
each semantic extension point to its exact Frobenius orbit and its unique
position in that orbit, discharging the former geometric orbit seam in the
middle Riemann--Roch calculation. -/
noncomputable def frobeniusClosedPointBridge25ThreeLE4 :
    ClosedPointBridge25ThreeLE4 frobeniusOrbitGrading25ThreeLE4 :=
  extensionFixedPointRealization25Three.pointOrbitClassification

end MazurProof.RationalPointsN25QuotientFrobeniusOrbits
