import FLT.Assumptions.MazurProof.RationalPointsN25QuotientBaseChange
import Mathlib.FieldTheory.Finite.Extension

/-!
# Finite-field and normalized-projective Frobenius descent

For a prime `p`, every field of cardinality `p^d` embeds in a common
Galois field whose extension degree is divisible by `d`.  Its image is
exactly the roots of `X^(p^d)-X`, hence exactly the coordinates fixed by the
`d`-th iterate of arithmetic Frobenius.

The second half of this file descends normalized projective charts
coordinate by coordinate.  It is independent of the equations defining a
curve.  Curve-specific modules only need to prove that their equations are
preserved and reflected by coefficient embeddings.
-/

namespace MazurProof.FiniteFieldFrobeniusDescent

open Polynomial
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientBaseChange

/-! ## The common finite field and its power-fixed subfields -/

/-- A canonical common finite field of characteristic `p`. -/
abbrev CommonField (p commonDegree : ℕ) [Fact (Nat.Prime p)] :=
  GaloisField p commonDegree

/-- The common field is represented as a finite type. -/
noncomputable instance commonFieldFintype
    (p commonDegree : ℕ) [Fact (Nat.Prime p)] :
    Fintype (CommonField p commonDegree) :=
  Fintype.ofFinite (CommonField p commonDegree)

/-- Embed the canonical degree-`d` Galois field in a common finite field.
Divisibility of extension degrees is the finite-field subfield criterion. -/
noncomputable def galoisFieldToCommon
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) :
    GaloisField p d →ₐ[ZMod p] CommonField p commonDegree :=
  (FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := GaloisField p d)
    (L := CommonField p commonDegree) (by
      rw [GaloisField.finrank p hdpos.ne',
        GaloisField.finrank p hCommonPos.ne']
      exact hd)).some

/-- Embed any finite characteristic-`p` field of cardinality `p^d` into the
common field.  The public result is a ring homomorphism, avoiding an algebra
instance diamond on the source field. -/
noncomputable def finiteFieldToCommon
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) :
    K →+* CommonField p commonDegree := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  exact ((galoisFieldToCommon p commonDegree d hdpos hCommonPos hd).comp
    (GaloisField.algEquivGaloisFieldOfFintype p d hcard).toAlgHom).toRingHom

/-- Roots in the common field of `X^(p^d)-X`. -/
def PowerFixed (p commonDegree d : ℕ) [Fact (Nat.Prime p)] :=
  {x : CommonField p commonDegree // x ^ (p ^ d) = x}

/-- The power-fixed subtype inherits finiteness from the common field. -/
noncomputable instance powerFixedFintype
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)] :
    Fintype (PowerFixed p commonDegree d) :=
  have : Finite (PowerFixed p commonDegree d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  Fintype.ofFinite (PowerFixed p commonDegree d)

/-- The finite-field embedding lands in the `p^d`-power fixed subtype by
the identity `a^(#K)=a`. -/
noncomputable def finiteFieldToPowerFixed
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) :
    K → PowerFixed p commonDegree d := by
  intro a
  refine ⟨finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard a, ?_⟩
  rw [← hcard, ← map_pow]
  exact congrArg
    (finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard)
    (FiniteField.pow_card a)

/-- The map into the power-fixed subtype is injective. -/
theorem finiteFieldToPowerFixed_injective
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) :
    Function.Injective
      (finiteFieldToPowerFixed p commonDegree K d hdpos hCommonPos hd hcard) := by
  intro a b hab
  apply (finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard).injective
  exact congrArg Subtype.val hab

/-- For positive `d`, `X^(p^d)-X` has degree `p^d`. -/
theorem commonPolynomial_natDegree
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)] (hd : 0 < d) :
    (X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).natDegree = p ^ d := by
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  calc
    (X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).natDegree =
        (X ^ (p ^ d) : (CommonField p commonDegree)[X]).natDegree :=
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
        rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
        exact one_lt_pow₀ hp hd.ne')
    _ = p ^ d := Polynomial.natDegree_X_pow
      (R := CommonField p commonDegree) (p ^ d)

/-- The fixed-subfield polynomial is nonzero in every positive degree. -/
theorem commonPolynomial_ne_zero
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)] (hd : 0 < d) :
    (X ^ (p ^ d) - X : (CommonField p commonDegree)[X]) ≠ 0 := by
  intro hzero
  have hdegree := congrArg Polynomial.natDegree hzero
  rw [commonPolynomial_natDegree p commonDegree d hd,
    Polynomial.natDegree_zero] at hdegree
  exact (pow_pos ((Fact.out : Nat.Prime p).pos) d).ne' hdegree

/-- A power-fixed element is a root of `X^(p^d)-X`. -/
noncomputable def powerFixedToRootSet
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)] (hd : 0 < d) :
    PowerFixed p commonDegree d ↪
      (X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).rootSet
        (CommonField p commonDegree) where
  toFun x := ⟨x.1, by
    rw [Polynomial.mem_rootSet]
    refine ⟨commonPolynomial_ne_zero p commonDegree d hd, ?_⟩
    simpa [Polynomial.aeval_def] using sub_eq_zero.mpr x.2⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : (X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).rootSet
        (CommonField p commonDegree) => z.1) hxy

/-- The root bound gives at most `p^d` power-fixed elements. -/
theorem powerFixed_card_le
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)] (hd : 0 < d) :
    Fintype.card (PowerFixed p commonDegree d) ≤ p ^ d := by
  letI : Fintype
      ((X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).rootSet
        (CommonField p commonDegree)) := Fintype.ofFinite _
  calc
    Fintype.card (PowerFixed p commonDegree d) ≤
        Fintype.card
          ((X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).rootSet
            (CommonField p commonDegree)) :=
      Fintype.card_le_of_injective _
        (powerFixedToRootSet p commonDegree d hd).injective
    _ = Set.ncard
          ((X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).rootSet
            (CommonField p commonDegree)) := by
      exact Set.fintypeCard_eq_ncard _
    _ ≤ (X ^ (p ^ d) - X : (CommonField p commonDegree)[X]).natDegree :=
      Polynomial.ncard_rootSet_le _ _
    _ = p ^ d := commonPolynomial_natDegree p commonDegree d hd

/-- The embedded field exhausts the power-fixed subtype.  The proof combines
embedding injectivity with the polynomial root bound; it does not choose an
arbitrary equivalence from a cardinality equation. -/
noncomputable def finiteFieldEquivPowerFixed
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) :
    K ≃ PowerFixed p commonDegree d := by
  let f := finiteFieldToPowerFixed p commonDegree K d hdpos hCommonPos hd hcard
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨finiteFieldToPowerFixed_injective
    p commonDegree K d hdpos hCommonPos hd hcard, ?_⟩
  apply Nat.le_antisymm
  · exact Fintype.card_le_of_injective f
      (finiteFieldToPowerFixed_injective
        p commonDegree K d hdpos hCommonPos hd hcard)
  · exact (powerFixed_card_le p commonDegree d hdpos).trans_eq hcard.symm

/-- The fixed-subfield equivalence is induced by the actual embedding. -/
@[simp]
theorem finiteFieldEquivPowerFixed_apply_val
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) (a : K) :
    (finiteFieldEquivPowerFixed p commonDegree K d hdpos hCommonPos hd hcard a).1 =
      finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard a := rfl

/-! ## Coherent finite-field realizations -/

/-- A source field realized as the `p^d`-power fixed subfield of the common
field.  The coherence law is essential: projective descent must use the same
chosen embedding both when it enters the common field and when fixed
coordinates are brought back to the source field. -/
structure Realization
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p] where
  embedding : K →+* CommonField p commonDegree
  fixedEquiv : K ≃ PowerFixed p commonDegree d
  fixedEquiv_apply_val : ∀ a : K, (fixedEquiv a).1 = embedding a

/-- Construct a coherent realization from the finite-field embedding and
the polynomial root bound.  Both components share the same embedding by
construction, so no uniqueness-of-choice argument is needed downstream. -/
noncomputable def realization
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) :
    Realization p commonDegree d K where
  embedding :=
    finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard
  fixedEquiv :=
    finiteFieldEquivPowerFixed p commonDegree K d hdpos hCommonPos hd hcard
  fixedEquiv_apply_val :=
    finiteFieldEquivPowerFixed_apply_val
      p commonDegree K d hdpos hCommonPos hd hcard

/-! ## Arithmetic Frobenius and normalized-projective descent -/

/-- Arithmetic Frobenius on the common finite field. -/
noncomputable def commonFrobenius
    (p commonDegree : ℕ) [Fact (Nat.Prime p)] :
    CommonField p commonDegree ≃ₐ[ZMod p] CommonField p commonDegree :=
  FiniteField.frobeniusAlgEquivOfAlgebraic
    (ZMod p) (CommonField p commonDegree)

/-- The `d`-th iterate of Frobenius is the `p^d`-power map. -/
theorem commonFrobenius_pow_apply
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (x : CommonField p commonDegree) :
    (commonFrobenius p commonDegree ^ d) x = x ^ (p ^ d) := by
  have h := congrFun
    (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate
      (ZMod p) (CommonField p commonDegree) d) x
  simpa [commonFrobenius, AlgEquiv.coe_pow, ZMod.card] using h

/-- Normalized projective points fixed by a Frobenius iterate. -/
def ProjectiveFrobeniusFixed
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)] :=
  {P : NormalizedProjective4 (CommonField p commonDegree) //
    NormalizedProjective4.map
      (commonFrobenius p commonDegree ^ d).toRingEquiv.toRingHom P = P}

/-- Every embedded source element is fixed by the corresponding Frobenius
iterate. -/
theorem finiteFieldToCommon_frobenius_fixed
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) (a : K) :
    (commonFrobenius p commonDegree ^ d)
        (finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard a) =
      finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard a := by
  rw [commonFrobenius_pow_apply]
  exact (finiteFieldToPowerFixed
    p commonDegree K d hdpos hCommonPos hd hcard a).2

/-- A Frobenius-fixed coordinate satisfies the power equation. -/
theorem frobenius_fixed_to_power_fixed
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (x : CommonField p commonDegree)
    (hx : (commonFrobenius p commonDegree ^ d) x = x) :
    x ^ (p ^ d) = x := by
  rw [← commonFrobenius_pow_apply]
  exact hx

/-- Descending an embedded element returns the original source element. -/
theorem finiteFieldEquivPowerFixed_symm_embedding
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d) (a : K)
    (ha : finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard a ^
        (p ^ d) =
      finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard a) :
    (finiteFieldEquivPowerFixed
      p commonDegree K d hdpos hCommonPos hd hcard).symm
      ⟨finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard a, ha⟩ = a := by
  let E := finiteFieldEquivPowerFixed
    p commonDegree K d hdpos hCommonPos hd hcard
  apply E.injective
  rw [E.apply_symm_apply]
  apply Subtype.ext
  rfl

/-- Re-embedding a descended power-fixed element recovers the common-field
coordinate. -/
theorem finiteFieldToCommon_symm_powerFixed
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (hdpos : 0 < d) (hCommonPos : 0 < commonDegree)
    (hd : d ∣ commonDegree) (hcard : Fintype.card K = p ^ d)
    (x : CommonField p commonDegree) (hx : x ^ (p ^ d) = x) :
    finiteFieldToCommon p commonDegree K d hdpos hCommonPos hd hcard
      ((finiteFieldEquivPowerFixed
        p commonDegree K d hdpos hCommonPos hd hcard).symm ⟨x, hx⟩) = x := by
  let E := finiteFieldEquivPowerFixed
    p commonDegree K d hdpos hCommonPos hd hcard
  have h := congrArg Subtype.val (E.apply_symm_apply ⟨x, hx⟩)
  exact h

/-- The embedding stored in a coherent realization lands in the appropriate
Frobenius-fixed subfield. -/
theorem Realization.embedding_frobenius_fixed
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (R : Realization p commonDegree d K) (a : K) :
    (commonFrobenius p commonDegree ^ d) (R.embedding a) = R.embedding a := by
  rw [commonFrobenius_pow_apply]
  simpa [R.fixedEquiv_apply_val a] using (R.fixedEquiv a).2

/-- Descending an embedded coordinate through the same realization returns
the original source coordinate. -/
theorem Realization.fixedEquiv_symm_embedding
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (R : Realization p commonDegree d K) (a : K)
    (ha : R.embedding a ^ (p ^ d) = R.embedding a) :
    R.fixedEquiv.symm ⟨R.embedding a, ha⟩ = a := by
  apply R.fixedEquiv.injective
  rw [R.fixedEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (R.fixedEquiv_apply_val a).symm

/-- Re-embedding a coordinate descended through a coherent realization
recovers the original fixed common-field coordinate. -/
theorem Realization.embedding_fixedEquiv_symm
    (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (R : Realization p commonDegree d K)
    (x : CommonField p commonDegree) (hx : x ^ (p ^ d) = x) :
    R.embedding (R.fixedEquiv.symm ⟨x, hx⟩) = x := by
  calc
    R.embedding (R.fixedEquiv.symm ⟨x, hx⟩) =
        (R.fixedEquiv (R.fixedEquiv.symm ⟨x, hx⟩)).1 :=
      (R.fixedEquiv_apply_val _).symm
    _ = x := congrArg Subtype.val (R.fixedEquiv.apply_symm_apply ⟨x, hx⟩)

/-- Degree-`d` normalized projective points are exactly the common-field
normalized points fixed by the `d`-th Frobenius iterate.  The inverse stays
in the existing normalized chart and descends only its free coordinates.
Both directions use one coherent finite-field realization. -/
noncomputable def projectiveEquivFrobeniusFixed
    (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (K : Type*) [Field K] [Fintype K] [CharP K p]
    (d : ℕ) (R : Realization p commonDegree d K) :
    NormalizedProjective4 K ≃ ProjectiveFrobeniusFixed p commonDegree d where
  toFun P := by
    refine ⟨NormalizedProjective4.map
      R.embedding P, ?_⟩
    cases P with
    | xChart y z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.xChart.injEq]
        exact ⟨by simpa using (Realization.embedding_frobenius_fixed
            p commonDegree d K R y),
          by simpa using (Realization.embedding_frobenius_fixed
            p commonDegree d K R z),
          by simpa using (Realization.embedding_frobenius_fixed
            p commonDegree d K R w)⟩
    | yChart z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.yChart.injEq]
        exact ⟨by simpa using (Realization.embedding_frobenius_fixed
            p commonDegree d K R z),
          by simpa using (Realization.embedding_frobenius_fixed
            p commonDegree d K R w)⟩
    | zChart w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.zChart.injEq]
        simpa using (Realization.embedding_frobenius_fixed
          p commonDegree d K R w)
    | wChart => rfl
  invFun P := by
    rcases P with ⟨P, hP⟩
    cases P with
    | xChart y z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.xChart.injEq] at hP
        exact .xChart
          (R.fixedEquiv.symm
            ⟨y, frobenius_fixed_to_power_fixed p commonDegree d y hP.1⟩)
          (R.fixedEquiv.symm
            ⟨z, frobenius_fixed_to_power_fixed p commonDegree d z hP.2.1⟩)
          (R.fixedEquiv.symm
            ⟨w, frobenius_fixed_to_power_fixed p commonDegree d w hP.2.2⟩)
    | yChart z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.yChart.injEq] at hP
        exact .yChart
          (R.fixedEquiv.symm
            ⟨z, frobenius_fixed_to_power_fixed p commonDegree d z hP.1⟩)
          (R.fixedEquiv.symm
            ⟨w, frobenius_fixed_to_power_fixed p commonDegree d w hP.2⟩)
    | zChart w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.zChart.injEq] at hP
        exact .zChart
          (R.fixedEquiv.symm
            ⟨w, frobenius_fixed_to_power_fixed p commonDegree d w hP⟩)
    | wChart => exact .wChart
  left_inv P := by
    cases P with
    | xChart y z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.xChart.injEq]
        exact ⟨by simpa using (Realization.fixedEquiv_symm_embedding
            p commonDegree d K R y _),
          by simpa using (Realization.fixedEquiv_symm_embedding
            p commonDegree d K R z _),
          by simpa using (Realization.fixedEquiv_symm_embedding
            p commonDegree d K R w _)⟩
    | yChart z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.yChart.injEq]
        exact ⟨by simpa using (Realization.fixedEquiv_symm_embedding
            p commonDegree d K R z _),
          by simpa using (Realization.fixedEquiv_symm_embedding
            p commonDegree d K R w _)⟩
    | zChart w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.zChart.injEq]
        simpa using (Realization.fixedEquiv_symm_embedding
          p commonDegree d K R w _)
    | wChart => rfl
  right_inv P := by
    apply Subtype.ext
    rcases P with ⟨P, hP⟩
    cases P with
    | xChart y z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.xChart.injEq] at hP ⊢
        exact ⟨by simpa using (Realization.embedding_fixedEquiv_symm
            p commonDegree d K R y _),
          by simpa using (Realization.embedding_fixedEquiv_symm
            p commonDegree d K R z _),
          by simpa using (Realization.embedding_fixedEquiv_symm
            p commonDegree d K R w _)⟩
    | yChart z w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.yChart.injEq] at hP ⊢
        exact ⟨by simpa using (Realization.embedding_fixedEquiv_symm
            p commonDegree d K R z _),
          by simpa using (Realization.embedding_fixedEquiv_symm
            p commonDegree d K R w _)⟩
    | zChart w =>
        simp only [NormalizedProjective4.map,
          NormalizedProjective4.zChart.injEq] at hP ⊢
        simpa using (Realization.embedding_fixedEquiv_symm
          p commonDegree d K R w _)
    | wChart => rfl

end MazurProof.FiniteFieldFrobeniusDescent
