import FLT.Assumptions.MazurProof.FiniteFieldFrobeniusDescent

/-!
# Frobenius descent for map-stable normalized-projective curves

This file restricts the characteristic-independent projective descent
equivalence to a curve predicate.  The only geometric input is that the
predicate is preserved and reflected by coefficient-field homomorphisms.
Equations, smoothness, genus, and point counts remain in characteristic-
specific modules.
-/

namespace MazurProof.NormalizedProjectiveCurveFrobenius

open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientBaseChange
open FiniteFieldFrobeniusDescent

/-- A normalized-projective curve predicate whose defining equations are
preserved and reflected by coefficient-field homomorphisms. -/
structure CurveModel where
  IsPoint : ∀ (K : Type) [Field K], NormalizedProjective4 K → Prop
  map_iff :
    ∀ {K L : Type} [Field K] [Field L]
      (f : K →+* L) (P : NormalizedProjective4 K),
      IsPoint L (NormalizedProjective4.map f P) ↔ IsPoint K P

/-- Curve points are normalized-projective points satisfying the selected
map-stable predicate. -/
abbrev CurvePoint (C : CurveModel) (K : Type) [Field K] :=
  {P : NormalizedProjective4 K // C.IsPoint K P}

/-- A coefficient-field homomorphism embeds curve points because the model
predicate is reflected as well as preserved. -/
def curvePointEmbedding
    (C : CurveModel) {K L : Type} [Field K] [Field L]
    (f : K →+* L) : CurvePoint C K ↪ CurvePoint C L where
  toFun P := ⟨NormalizedProjective4.map f P.1, (C.map_iff f P.1).2 P.2⟩
  inj' := by
    intro P Q hPQ
    apply Subtype.ext
    exact NormalizedProjective4.map_injective f f.injective
      (congrArg Subtype.val hPQ)

/-- A coefficient-field equivalence induces an equivalence of curve-point
types by coordinatewise base change. -/
def curvePointEquiv
    (C : CurveModel) {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) : CurvePoint C K ≃ CurvePoint C L where
  toFun := curvePointEmbedding C e.toRingHom
  invFun := curvePointEmbedding C e.symm.toRingHom
  left_inv P := by
    apply Subtype.ext
    cases P with
    | mk P hP =>
      cases P <;> simp [curvePointEmbedding, NormalizedProjective4.map]
  right_inv P := by
    apply Subtype.ext
    cases P with
    | mk P hP =>
      cases P <;> simp [curvePointEmbedding, NormalizedProjective4.map]

/-- The underlying coordinatewise arithmetic-Frobenius function on common
curve points.  Naming the function separately keeps iteration from unfolding
the proof fields of an equivalence. -/
noncomputable def pointFrobeniusFun
    (C : CurveModel) (p commonDegree : ℕ) [Fact (Nat.Prime p)] :
    CurvePoint C (CommonField p commonDegree) →
      CurvePoint C (CommonField p commonDegree) :=
  curvePointEmbedding C
    (commonFrobenius p commonDegree).toRingEquiv.toRingHom

/-- Arithmetic Frobenius as a permutation of common-field curve points. -/
noncomputable def pointFrobenius
    (C : CurveModel) (p commonDegree : ℕ) [Fact (Nat.Prime p)] :
    Equiv.Perm (CurvePoint C (CommonField p commonDegree)) where
  toFun := pointFrobeniusFun C p commonDegree
  invFun := curvePointEmbedding C
    (commonFrobenius p commonDegree).symm.toRingEquiv.toRingHom
  left_inv P := by
    apply Subtype.ext
    change NormalizedProjective4.map
        (commonFrobenius p commonDegree).symm.toRingEquiv.toRingHom
        (NormalizedProjective4.map
          (commonFrobenius p commonDegree).toRingEquiv.toRingHom P.1) = P.1
    rw [NormalizedProjective4.map_comp]
    have hcomp :
        (commonFrobenius p commonDegree).symm.toRingEquiv.toRingHom.comp
          (commonFrobenius p commonDegree).toRingEquiv.toRingHom =
            RingHom.id (CommonField p commonDegree) := by
      ext x
      simp
    rw [hcomp, NormalizedProjective4.map_id]
  right_inv P := by
    apply Subtype.ext
    change NormalizedProjective4.map
        (commonFrobenius p commonDegree).toRingEquiv.toRingHom
        (NormalizedProjective4.map
          (commonFrobenius p commonDegree).symm.toRingEquiv.toRingHom P.1) = P.1
    rw [NormalizedProjective4.map_comp]
    have hcomp :
        (commonFrobenius p commonDegree).toRingEquiv.toRingHom.comp
          (commonFrobenius p commonDegree).symm.toRingEquiv.toRingHom =
            RingHom.id (CommonField p commonDegree) := by
      ext x
      simp
    rw [hcomp, NormalizedProjective4.map_id]

/-- One point-Frobenius step is coordinatewise arithmetic Frobenius on the
underlying normalized-projective point. -/
@[simp]
theorem pointFrobenius_apply_val
    (C : CurveModel) (p commonDegree : ℕ) [Fact (Nat.Prime p)]
    (P : CurvePoint C (CommonField p commonDegree)) :
    (pointFrobenius C p commonDegree P).1 =
      NormalizedProjective4.map
        (commonFrobenius p commonDegree).toRingEquiv.toRingHom P.1 := rfl

/-- One application of a map commutes with any iterate of the same map.
This isolates a small function-iteration normalization used in the chart
calculation below. -/
theorem self_iterate_commute_apply {A : Type*}
    (f : A → A) (d : ℕ) (x : A) :
    f (f^[d] x) = f^[d] (f x) := by
  calc
    f (f^[d] x) = f^[1] (f^[d] x) := rfl
    _ = f^[1 + d] x := (Function.iterate_add_apply f 1 d x).symm
    _ = f^[d + 1] x := by rw [Nat.add_comm]
    _ = f^[d] (f^[1] x) := Function.iterate_add_apply f d 1 x
    _ = f^[d] (f x) := rfl

set_option maxHeartbeats 800000 in
-- Function iteration over a predicate subtype needs extra elaboration.
/-- Iterating point Frobenius applies the corresponding iterated field
Frobenius to every free normalized-projective coordinate. -/
theorem pointFrobenius_iterate_val
    (C : CurveModel) (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (P : CurvePoint C (CommonField p commonDegree)) :
    (((pointFrobeniusFun C p commonDegree :
        CurvePoint C (CommonField p commonDegree) →
          CurvePoint C (CommonField p commonDegree))^[d]) P).1 =
      NormalizedProjective4.map
        (commonFrobenius p commonDegree ^ d).toRingEquiv.toRingHom P.1 := by
  induction d with
  | zero =>
      change P.1 = NormalizedProjective4.map
        (RingHom.id (CommonField p commonDegree)) P.1
      exact (NormalizedProjective4.map_id P.1).symm
  | succ d ih =>
      rw [Function.iterate_succ_apply']
      rw [show (pointFrobeniusFun C p commonDegree
          (((pointFrobeniusFun C p commonDegree :
            CurvePoint C (CommonField p commonDegree) →
              CurvePoint C (CommonField p commonDegree))^[d]) P)).1 =
          NormalizedProjective4.map
            (commonFrobenius p commonDegree).toRingEquiv.toRingHom
            (((pointFrobeniusFun C p commonDegree :
              CurvePoint C (CommonField p commonDegree) →
                CurvePoint C (CommonField p commonDegree))^[d]) P).1 from rfl,
        ih,
        NormalizedProjective4.map_comp]
      cases P.1 <;>
        simp [NormalizedProjective4.map, pow_succ,
          self_iterate_commute_apply]

set_option maxHeartbeats 800000 in
-- Keep the fixed-point subtype definition aligned with the iteration theorem.
/-- Common-field curve points fixed by the `d`-th arithmetic-Frobenius
iterate. -/
abbrev FixedByIterate
    (C : CurveModel) (p commonDegree d : ℕ) [Fact (Nat.Prime p)] :=
  {P : CurvePoint C (CommonField p commonDegree) //
    ((pointFrobeniusFun C p commonDegree :
      CurvePoint C (CommonField p commonDegree) →
        CurvePoint C (CommonField p commonDegree))^[d]) P = P}

/-- Curve points over a realized degree-`d` field are exactly common-field
curve points fixed by the `d`-th arithmetic-Frobenius iterate.  The proof
restricts explicit chartwise descent and never uses the cardinality of a
curve-point type. -/
noncomputable def curvePointEquivFixedByIterate
    (C : CurveModel) (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (R : Realization p commonDegree d K) :
    CurvePoint C K ≃ FixedByIterate C p commonDegree d where
  toFun P := by
    let PR := projectiveEquivFrobeniusFixed p commonDegree K d R P.1
    let Q : CurvePoint C (CommonField p commonDegree) :=
      ⟨PR.1, by
        rw [show PR.1 = NormalizedProjective4.map R.embedding P.1 from rfl]
        exact (C.map_iff R.embedding P.1).2 P.2⟩
    refine ⟨Q, ?_⟩
    apply Subtype.ext
    rw [pointFrobenius_iterate_val]
    exact PR.2
  invFun Q := by
    have hraw : NormalizedProjective4.map
        (commonFrobenius p commonDegree ^ d).toRingEquiv.toRingHom Q.1.1 =
          Q.1.1 := by
      have h := congrArg Subtype.val Q.2
      rw [pointFrobenius_iterate_val] at h
      exact h
    let PR : ProjectiveFrobeniusFixed p commonDegree d := ⟨Q.1.1, hraw⟩
    let P := (projectiveEquivFrobeniusFixed p commonDegree K d R).symm PR
    refine ⟨P, ?_⟩
    apply (C.map_iff R.embedding P).1
    have hPR := congrArg Subtype.val
      ((projectiveEquivFrobeniusFixed p commonDegree K d R).apply_symm_apply PR)
    rw [show NormalizedProjective4.map R.embedding P = PR.1 from hPR]
    exact Q.1.2
  left_inv P := by
    apply Subtype.ext
    let E := projectiveEquivFrobeniusFixed p commonDegree K d R
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    let E := projectiveEquivFrobeniusFixed p commonDegree K d R
    have hraw : NormalizedProjective4.map
        (commonFrobenius p commonDegree ^ d).toRingEquiv.toRingHom Q.1.1 =
          Q.1.1 := by
      have h := congrArg Subtype.val Q.2
      rw [pointFrobenius_iterate_val] at h
      exact h
    let PR : ProjectiveFrobeniusFixed p commonDegree d := ⟨Q.1.1, hraw⟩
    simpa only [E, PR] using congrArg Subtype.val (E.apply_symm_apply PR)

/-- The forward curve descent map is the coordinatewise embedding stored in
the coherent finite-field realization. -/
@[simp]
theorem curvePointEquivFixedByIterate_apply_val
    (C : CurveModel) (p commonDegree d : ℕ) [Fact (Nat.Prime p)]
    (K : Type) [Field K] [Fintype K] [CharP K p]
    (R : Realization p commonDegree d K) (P : CurvePoint C K) :
    ((curvePointEquivFixedByIterate C p commonDegree d K R P).1).1 =
      NormalizedProjective4.map R.embedding P.1 := rfl

end MazurProof.NormalizedProjectiveCurveFrobenius
