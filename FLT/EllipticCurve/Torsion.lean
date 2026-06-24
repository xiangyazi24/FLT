/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Instances.ZMod
public import FLT.Deformations.RepresentationTheory.GaloisRep
public import scratch.KeystoneEDS
public import scratch.SeamE1

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine
open scoped DirectSum Function

/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n

--variable (n : ℕ) in
--#synth AddCommGroup (E.nTorsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry

namespace KeystoneNTorsion

variable {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

private noncomputable def nTorsionEquivKernel (n : ℕ) :
    W.nTorsion n ≃ {P : (W⁄k).Point // n • P = 0} where
  toFun P := ⟨P.1, by
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP
    simpa only [natCast_zsmul] using hP⟩
  invFun P := ⟨P.1, by
    rw [Submodule.mem_torsionBy_iff]
    simpa only [natCast_zsmul] using P.2⟩
  left_inv P := by
    ext
    rfl
  right_inv P := by
    ext
    rfl

/-- SEAM 1 (étaleness of [n]): the non-2-torsion division polynomial is separable when
char ∤ n. To be discharged later via formal group (E1) or resultant identity (E2). -/
theorem preΨ'_separable_of_natCast_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable :=
  WeierstrassCurve.preΨ'_separable_of_natCast_ne_zero W hn

/-- SEAM 2 (x-coordinate division polynomial formula), stated in the direct form needed for
kernel membership. This is the `xRep_zsmul_some_eq_divisionPolynomial` seam after extracting the
zero-denominator criterion. -/
theorem nsmul_eq_zero_iff_ΨSq_eval {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by
  have h4 : (4 : k) ≠ 0 := sorry
  have hψ_ne : ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := sorry
  have hc3 : W.Ψ₃ ≠ 0 := sorry
  have key := KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval (W := W) h4 hψ_ne hc3 (n := n) h
  convert key using 3
  congr
  exact Subsingleton.elim _ _

lemma two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero {x y : k} (h : (W⁄k).Nonsingular x y) :
    2 • (Point.some x y h : (W⁄k).Point) = 0 ↔ W.Ψ₂Sq.eval x = 0 := by
  simpa using (nsmul_eq_zero_iff_ΨSq_eval (W := W) (n := 2) h)

lemma nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero {n : ℕ} {x y : k}
    (h : (W⁄k).Nonsingular x y) (h₂ : 2 • (Point.some x y h : (W⁄k).Point) ≠ 0) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.preΨ' n).eval x = 0 := by
  classical
  rw [nsmul_eq_zero_iff_ΨSq_eval (W := W) (n := n) h]
  have hΨ₂ : W.Ψ₂Sq.eval x ≠ 0 := by
    exact mt (two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero (W := W) h).mpr h₂
  rw [W.ΨSq_ofNat n]
  by_cases hn_even : Even n
  · simp [hn_even, hΨ₂, mul_eq_zero, pow_eq_zero_iff]
  · simp [hn_even, pow_eq_zero_iff]

lemma preΨ'_rootSet_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Fintype.card ((W.preΨ' n).rootSet k) =
      (n ^ 2 - if Even n then 4 else 1) / 2 := by
  rw [Polynomial.card_rootSet_eq_natDegree
    (preΨ'_separable_of_natCast_ne_zero (W := W) hn)
    (IsSepClosed.splits_domain (W.preΨ' n)
      (preΨ'_separable_of_natCast_ne_zero (W := W) hn))]
  exact W.natDegree_preΨ' hn

theorem preΨ'_eval_eq_zero_iff_exists_non_two_torsion [IsSepClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) {x : k} :
    (W.preΨ' n).eval x = 0 ↔
      ∃ y, ∃ h : (W⁄k).Nonsingular x y,
        2 • (Point.some x y h : (W⁄k).Point) ≠ 0 ∧
          n • (Point.some x y h : (W⁄k).Point) = 0 := by
  constructor
  · intro hx
    -- TODO: no-spurious-roots / point realization over a separably closed field.
    sorry
  · rintro ⟨y, h, h₂, hnP⟩
    exact (nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
      (W := W) h h₂).mp hnP

omit [DecidableEq k] [W.IsElliptic] in
private lemma rootSet_eval_eq_zero {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) :
    (W.preΨ' n).eval x.1 = 0 := by
  have hne : W.preΨ' n ≠ 0 := W.preΨ'_ne_zero hn
  simpa using (Polynomial.mem_rootSet_of_ne hne).mp x.2

private noncomputable def rootPointExists [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) :
    ∃ y, ∃ h : (W⁄k).Nonsingular x.1 y,
      2 • (Point.some x.1 y h : (W⁄k).Point) ≠ 0 ∧
        n • (Point.some x.1 y h : (W⁄k).Point) = 0 :=
  (preΨ'_eval_eq_zero_iff_exists_non_two_torsion (W := W) hn).mp
    (rootSet_eval_eq_zero (W := W) hn x)

private noncomputable def rootY [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) : k :=
  Classical.choose (rootPointExists (W := W) hn x)

private noncomputable def rootNonsingular [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) : (W⁄k).Nonsingular x.1 (rootY (W := W) hn x) :=
  Classical.choose (Classical.choose_spec (rootPointExists (W := W) hn x))

private noncomputable def rootPoint [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) : (W⁄k).Point :=
  Point.some x.1 (rootY (W := W) hn x) (rootNonsingular (W := W) hn x)

private lemma rootPoint_two_ne_zero [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) :
    2 • rootPoint (W := W) hn x ≠ 0 := by
  exact (Classical.choose_spec
    (Classical.choose_spec (rootPointExists (W := W) hn x))).1

private lemma rootPoint_nsmul_eq_zero [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) :
    n • rootPoint (W := W) hn x = 0 := by
  exact (Classical.choose_spec
    (Classical.choose_spec (rootPointExists (W := W) hn x))).2

private lemma rootPoint_xRep [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) :
    (rootPoint (W := W) hn x).xRep = ![x.1, 1] := by
  simp [rootPoint]

private abbrev NonTwoKernel (n : ℕ) : Type _ :=
  {P : (W⁄k).Point // n • P = 0 ∧ 2 • P ≠ 0}

private abbrev TwoKernel (n : ℕ) : Type _ :=
  {P : (W⁄k).Point // n • P = 0 ∧ 2 • P = 0}

private abbrev TwoTorsionKernel : Type _ :=
  {P : (W⁄k).Point // 2 • P = 0}

private lemma four_ne_zero_of_two_ne_zero (h₂ : (2 : k) ≠ 0) : (4 : k) ≠ 0 := by
  have h : (2 : k) * (2 : k) ≠ 0 := mul_ne_zero h₂ h₂
  simpa [show (4 : k) = (2 : k) * (2 : k) by norm_num] using h

private lemma affine_two_torsion_y_eq_negY {x y : k} {h : (W⁄k).Nonsingular x y}
    (h2 : 2 • (Point.some x y h : (W⁄k).Point) = 0) :
    y = (W⁄k).negY x y := by
  rw [two_nsmul] at h2
  by_contra hy
  have hs :
      (Point.some x y h : (W⁄k).Point) + Point.some x y h =
        Point.some _ _ (nonsingular_add h h (fun hxy => hy hxy.right)) :=
    Point.add_self_of_Y_ne hy
  rw [h2] at hs
  exact Point.some_ne_zero _ hs.symm

private lemma affine_two_torsion_linear_relation {x y : k} {h : (W⁄k).Nonsingular x y}
    (h2 : 2 • (Point.some x y h : (W⁄k).Point) = 0) :
    2 * y + (W⁄k).a₁ * x + (W⁄k).a₃ = 0 := by
  have hy := affine_two_torsion_y_eq_negY (W := W) h2
  rw [negY] at hy
  linear_combination hy

private noncomputable def twoTorsionY (h₂ : (2 : k) ≠ 0) (x : k) : k :=
  -((W⁄k).a₁ * x + (W⁄k).a₃) / 2

private lemma twoTorsionY_linear_relation (h₂ : (2 : k) ≠ 0) (x : k) :
    2 * twoTorsionY (W := W) h₂ x + (W⁄k).a₁ * x + (W⁄k).a₃ = 0 := by
  unfold twoTorsionY
  field_simp [h₂]
  ring

private lemma twoTorsionY_eq_negY (h₂ : (2 : k) ≠ 0) (x : k) :
    twoTorsionY (W := W) h₂ x = (W⁄k).negY x (twoTorsionY (W := W) h₂ x) := by
  have hlin := twoTorsionY_linear_relation (W := W) h₂ x
  rw [negY]
  linear_combination hlin

private lemma equation_of_Ψ₂Sq_eval_eq_zero_of_linear {x y : k}
    (hroot : (W⁄k).Ψ₂Sq.eval x = 0)
    (hlin : 2 * y + (W⁄k).a₁ * x + (W⁄k).a₃ = 0) (h₂ : (2 : k) ≠ 0) :
    (W⁄k).Equation x y := by
  rw [equation_iff']
  have h4 : (4 : k) ≠ 0 := four_ne_zero_of_two_ne_zero h₂
  let q :=
    y ^ 2 + (W⁄k).a₁ * x * y + (W⁄k).a₃ * y -
      (x ^ 3 + (W⁄k).a₂ * x ^ 2 + (W⁄k).a₄ * x + (W⁄k).a₆)
  have h4q : (4 : k) * q = 0 := by
    calc
      (4 : k) * q =
          (2 * y + (W⁄k).a₁ * x + (W⁄k).a₃) ^ 2 - (W⁄k).Ψ₂Sq.eval x := by
            simp [q, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
              WeierstrassCurve.b₆]
            ring
      _ = 0 := by
            rw [hlin, hroot]
            ring
  exact (mul_eq_zero.mp h4q).resolve_left h4

private lemma twoTorsionY_nonsingular_of_Ψ₂Sq_eval_eq_zero (h₂ : (2 : k) ≠ 0) {x : k}
    (hroot : (W⁄k).Ψ₂Sq.eval x = 0) :
    (W⁄k).Nonsingular x (twoTorsionY (W := W) h₂ x) := by
  haveI : (W⁄k).IsElliptic := by
    change (W.map (algebraMap k k)).IsElliptic
    infer_instance
  exact (equation_iff_nonsingular (W := W⁄k)).mp
    (equation_of_Ψ₂Sq_eval_eq_zero_of_linear (W := W) hroot
      (twoTorsionY_linear_relation (W := W) h₂ x) h₂)

private lemma twoTorsionY_two_nsmul_eq_zero (h₂ : (2 : k) ≠ 0) {x : k}
    (hroot : (W⁄k).Ψ₂Sq.eval x = 0) :
    2 • (Point.some x (twoTorsionY (W := W) h₂ x)
        (twoTorsionY_nonsingular_of_Ψ₂Sq_eval_eq_zero (W := W) h₂ hroot) :
      (W⁄k).Point) = 0 := by
  rw [two_nsmul]
  exact Point.add_self_of_Y_eq (twoTorsionY_eq_negY (W := W) h₂ x)

private lemma cubic_toPoly_discr_eq {P : Cubic k} (ha : P.a ≠ 0) :
    P.toPoly.discr = P.discr := by
  rw [Polynomial.discr_of_degree_eq_three (Cubic.degree_of_a_ne_zero ha)]
  simp [Cubic.discr]

private lemma cubic_toPoly_separable_of_discr_ne_zero {P : Cubic k} (ha : P.a ≠ 0)
    (hdisc : P.discr ≠ 0) : P.toPoly.Separable := by
  rw [Polynomial.separable_def]
  by_contra hcop
  let f := P.toPoly
  have hf0 : f ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
  have hres0 : Polynomial.resultant f f.derivative = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    exact ⟨Or.inl hf0, hcop⟩
  have hpos : 0 < f.degree := by
    rw [show f = P.toPoly by rfl, Cubic.degree_of_a_ne_zero ha]
    norm_num
  have hraw_ne : Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
    rw [Polynomial.resultant_deriv hpos]
    have hlc : f.leadingCoeff = P.a := Cubic.leadingCoeff_of_a_ne_zero ha
    have hdisc' : f.discr = P.discr := cubic_toPoly_discr_eq ha
    rw [hlc, hdisc']
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ha) hdisc
  have hle : f.derivative.natDegree ≤ f.natDegree - 1 := Polynomial.natDegree_derivative_le f
  let r := f.natDegree - 1 - f.derivative.natDegree
  have hraw_eq : Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1) =
      f.coeff f.natDegree ^ r * Polynomial.resultant f f.derivative := by
    have hr : f.natDegree - 1 = f.derivative.natDegree + r := by
      exact (Nat.add_sub_of_le hle).symm
    rw [hr]
    exact Polynomial.resultant_add_right_deg (f := f) (g := f.derivative)
      (m := f.natDegree) (n := f.derivative.natDegree) r (le_refl _)
  have hraw_zero : Polynomial.resultant f f.derivative f.natDegree (f.natDegree - 1) = 0 := by
    rw [hraw_eq, hres0, mul_zero]
  exact hraw_ne hraw_zero

private lemma twoTorsion_Ψ₂Sq_rootSet_card [IsSepClosed k] (h₂ : (2 : k) ≠ 0) :
    Fintype.card (((W⁄k).Ψ₂Sq).rootSet k) = 3 := by
  haveI : (W⁄k).IsElliptic := by
    change (W.map (algebraMap k k)).IsElliptic
    infer_instance
  let P := (W⁄k).twoTorsionPolynomial
  have ha : P.a ≠ 0 := by
    change (4 : k) ≠ 0
    exact four_ne_zero_of_two_ne_zero h₂
  have hdisc : P.discr ≠ 0 := by
    exact (W⁄k).twoTorsionPolynomial_discr_ne_zero_of_isElliptic
      (isUnit_iff_ne_zero.mpr h₂)
  have hsep : P.toPoly.Separable := cubic_toPoly_separable_of_discr_ne_zero ha hdisc
  have hsplit : (P.toPoly.map (algebraMap k k)).Splits :=
    IsSepClosed.splits_domain P.toPoly hsep
  have hcubic : (Cubic.map (algebraMap k k) P).roots.toFinset.card = 3 :=
    Cubic.card_roots_of_discr_ne_zero (P := P) (φ := algebraMap k k) ha hsplit hdisc
  rw [Set.fintypeCard_eq_ncard]
  rw [WeierstrassCurve.Ψ₂Sq_eq]
  rw [Polynomial.rootSet_def, Polynomial.aroots_def, Set.ncard_coe_finset]
  simpa [P, Cubic.map_roots] using hcubic

private noncomputable def twoTorsionKernelEquivRootOption (h₂ : (2 : k) ≠ 0) :
    TwoTorsionKernel (W := W) ≃ Option (((W⁄k).Ψ₂Sq).rootSet k) where
  toFun P :=
    match P with
    | ⟨Point.zero, _⟩ => none
    | ⟨Point.some x y h, hP⟩ =>
        haveI : (W⁄k).IsElliptic := by
          change (W.map (algebraMap k k)).IsElliptic
          infer_instance
        have h4 : (4 : k) ≠ 0 := four_ne_zero_of_two_ne_zero h₂
        some ⟨x, (Polynomial.mem_rootSet_of_ne ((W⁄k).Ψ₂Sq_ne_zero h4)).mpr <| by
          simpa using (two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero (W := W⁄k) h).mp hP⟩
  invFun
    | none => ⟨0, by simp⟩
    | some xr =>
        have h4 : (4 : k) ≠ 0 := four_ne_zero_of_two_ne_zero h₂
        let hroot : (W⁄k).Ψ₂Sq.eval xr.1 = 0 :=
          (Polynomial.mem_rootSet_of_ne ((W⁄k).Ψ₂Sq_ne_zero h4)).mp xr.2
        ⟨Point.some xr.1 (twoTorsionY (W := W) h₂ xr.1)
            (twoTorsionY_nonsingular_of_Ψ₂Sq_eval_eq_zero (W := W) h₂ hroot),
          twoTorsionY_two_nsmul_eq_zero (W := W) h₂ hroot⟩
  left_inv P := by
    rcases P with ⟨P, hP⟩
    cases P with
    | zero =>
        ext
        rfl
    | some x y h =>
        haveI : (W⁄k).IsElliptic := by
          change (W.map (algebraMap k k)).IsElliptic
          infer_instance
        dsimp
        have hlin := affine_two_torsion_linear_relation (W := W) hP
        have hlin' := twoTorsionY_linear_relation (W := W) h₂ x
        have hy : y = twoTorsionY (W := W) h₂ x := by
          have hmul : (2 : k) * (y - twoTorsionY (W := W) h₂ x) = 0 := by
            linear_combination hlin - hlin'
          exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left h₂)
        subst hy
        ext
        rfl
  right_inv xr := by
    cases xr with
    | none => rfl
    | some xr =>
        have h4 : (4 : k) ≠ 0 := four_ne_zero_of_two_ne_zero h₂
        have hroot : (W⁄k).Ψ₂Sq.eval xr.1 = 0 :=
          (Polynomial.mem_rootSet_of_ne ((W⁄k).Ψ₂Sq_ne_zero h4)).mp xr.2
        ext
        rfl

private noncomputable def signedRootPoint [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0)
    (x : (W.preΨ' n).rootSet k) : Bool → NonTwoKernel (W := W) n
  | false =>
      ⟨rootPoint (W := W) hn x,
        rootPoint_nsmul_eq_zero (W := W) hn x,
        rootPoint_two_ne_zero (W := W) hn x⟩
  | true =>
      ⟨-rootPoint (W := W) hn x, by
        constructor
        · simpa using congrArg Neg.neg (rootPoint_nsmul_eq_zero (W := W) hn x)
        · intro h₂
          exact rootPoint_two_ne_zero (W := W) hn x (by simpa using congrArg Neg.neg h₂)⟩

omit [W.IsElliptic] in
lemma ne_neg_of_two_nsmul_ne_zero {P : (W⁄k).Point} (h₂ : 2 • P ≠ 0) : P ≠ -P := by
  intro h
  apply h₂
  calc
    2 • P = P + P := by simp [two_nsmul]
    _ = P + -P := by nth_rw 2 [h]
    _ = 0 := add_neg_cancel P

private noncomputable def nonTwoKernelEquivRootBool [IsSepClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) :
    NonTwoKernel (W := W) n ≃ (Σ _x : (W.preΨ' n).rootSet k, Bool) where
  toFun P :=
    match P with
    | ⟨Point.zero, hP⟩ => False.elim (hP.2 (by rw [← Point.zero_def, nsmul_zero]))
    | ⟨Point.some x y h, hP⟩ =>
        let hxpre : (W.preΨ' n).eval x = 0 :=
          (nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
            (W := W) h hP.2).mp hP.1
        let xr : (W.preΨ' n).rootSet k :=
          ⟨x, (Polynomial.mem_rootSet_of_ne (W.preΨ'_ne_zero hn)).mpr (by simpa using hxpre)⟩
        if (Point.some x y h : (W⁄k).Point) = rootPoint (W := W) hn xr then
          ⟨xr, false⟩
        else
          ⟨xr, true⟩
  invFun xb := signedRootPoint (W := W) hn xb.1 xb.2
  left_inv P := by
    rcases P with ⟨P, hnP, h₂P⟩
    cases P with
    | zero =>
        exact False.elim (h₂P (by rw [← Point.zero_def, nsmul_zero]))
    | some x y h =>
        dsimp
        let hxpre : (W.preΨ' n).eval x = 0 :=
          (nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero
            (W := W) h h₂P).mp hnP
        let xr : (W.preΨ' n).rootSet k :=
          ⟨x, (Polynomial.mem_rootSet_of_ne (W.preΨ'_ne_zero hn)).mpr (by simpa using hxpre)⟩
        by_cases hEq : (Point.some x y h : (W⁄k).Point) = rootPoint (W := W) hn xr
        · simp [hEq, signedRootPoint, xr]
        · have hxrep :
              (Point.some x y h : (W⁄k).Point).xRep =
                (rootPoint (W := W) hn xr).xRep := by
            simp [rootPoint_xRep (W := W) hn xr, xr]
          have h_or := (Point.xRep_eq_xRep_iff (W := W⁄k)).mp hxrep
          rcases h_or with hsame | hneg
          · exact False.elim (hEq hsame)
          · have hnot :
                ¬(-rootPoint (W := W) hn xr = rootPoint (W := W) hn xr) := by
              intro hroot
              have hroot' : rootPoint (W := W) hn xr = -rootPoint (W := W) hn xr := by
                simpa [eq_comm] using hroot
              exact ne_neg_of_two_nsmul_ne_zero (W := W)
                (rootPoint_two_ne_zero (W := W) hn xr) hroot'
            simp [signedRootPoint, hneg, xr, hnot]
  right_inv xb := by
    rcases xb with ⟨xr, b⟩
    cases b
    · ext <;> simp [signedRootPoint, rootPoint]
    · have hpoint_ne :
          ¬(-rootPoint (W := W) hn xr = rootPoint (W := W) hn xr) := by
        intro hEq
        have hEq' : rootPoint (W := W) hn xr = -rootPoint (W := W) hn xr := by
          simpa [eq_comm] using hEq
        exact ne_neg_of_two_nsmul_ne_zero (W := W)
          (rootPoint_two_ne_zero (W := W) hn xr) hEq'
      have hy_ne :
          ¬(-rootY (W := W) hn xr - W.a₁ * xr.1 - W.a₃ = rootY (W := W) hn xr) := by
        intro hy
        apply hpoint_ne
        simp [rootPoint, hy]
      ext <;> simp [signedRootPoint, rootPoint, hy_ne]

private lemma nonTwoKernel_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (NonTwoKernel (W := W) n) =
      2 * ((n ^ 2 - if Even n then 4 else 1) / 2) := by
  classical
  have hbool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  calc
    Nat.card (NonTwoKernel (W := W) n)
        = Nat.card (Σ _x : (W.preΨ' n).rootSet k, Bool) :=
          Nat.card_congr (nonTwoKernelEquivRootBool (W := W) hn)
    _ = ∑ _x : (W.preΨ' n).rootSet k, Nat.card Bool := by
          rw [Nat.card_sigma]
    _ = ∑ _x : (W.preΨ' n).rootSet k, 2 := by
          simp only [hbool]
    _ = Fintype.card ((W.preΨ' n).rootSet k) * 2 := by
          simp
    _ = 2 * ((n ^ 2 - if Even n then 4 else 1) / 2) := by
          rw [preΨ'_rootSet_card (W := W) hn]
          omega

private theorem twoTorsionKernel_card [IsSepClosed k] (h₂ : (2 : k) ≠ 0) :
    Nat.card (TwoTorsionKernel (W := W)) = 4 := by
  classical
  calc
    Nat.card (TwoTorsionKernel (W := W))
        = Nat.card (Option (((W⁄k).Ψ₂Sq).rootSet k)) :=
          Nat.card_congr (twoTorsionKernelEquivRootOption (W := W) h₂)
    _ = Fintype.card (Option (((W⁄k).Ψ₂Sq).rootSet k)) := by
          rw [Nat.card_eq_fintype_card]
    _ = Fintype.card (((W⁄k).Ψ₂Sq).rootSet k) + 1 := by
          rw [Fintype.card_option]
    _ = 4 := by
          rw [twoTorsion_Ψ₂Sq_rootSet_card (W := W) h₂]

omit [DecidableEq k] in
private lemma two_ne_zero_of_even_natCast_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) (hn_even : Even n) :
    (2 : k) ≠ 0 := by
  intro h₂
  rcases hn_even with ⟨m, rfl⟩
  apply hn
  rw [Nat.cast_add, ← two_mul, h₂, zero_mul]

private noncomputable def twoKernelEvenEquiv {n : ℕ} (hn_even : Even n) :
    TwoKernel (W := W) n ≃ TwoTorsionKernel (W := W) where
  toFun P := ⟨P.1, P.2.2⟩
  invFun P := ⟨P.1, by
    constructor
    · rcases hn_even with ⟨m, rfl⟩
      rw [add_nsmul, ← nsmul_add, ← two_nsmul (P : (W⁄k).Point), P.2, nsmul_zero]
    · exact P.2⟩
  left_inv P := by
    ext
    rfl
  right_inv P := by
    ext
    rfl

private lemma odd_nsmul_eq_self_of_two_nsmul_eq_zero {G : Type*} [AddCommMonoid G]
    {n : ℕ} (hn_odd : Odd n) {P : G} (h₂ : 2 • P = 0) : n • P = P := by
  rcases hn_odd with ⟨m, rfl⟩
  simp [add_nsmul, mul_nsmul, h₂]

private noncomputable def twoKernelOddEquiv {n : ℕ} (hn_odd : Odd n) :
    TwoKernel (W := W) n ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0, by simp⟩
  left_inv P := by
    rcases P with ⟨P, hnP, h₂P⟩
    have hP : P = 0 := by
      simpa [odd_nsmul_eq_self_of_two_nsmul_eq_zero hn_odd h₂P] using hnP
    ext
    exact hP.symm
  right_inv _ := rfl

private lemma twoKernel_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (TwoKernel (W := W) n) = if Even n then 4 else 1 := by
  classical
  by_cases hn_even : Even n
  · rw [if_pos hn_even]
    calc
      Nat.card (TwoKernel (W := W) n)
          = Nat.card (TwoTorsionKernel (W := W)) :=
            Nat.card_congr (twoKernelEvenEquiv (W := W) hn_even)
      _ = 4 := twoTorsionKernel_card (W := W)
        (two_ne_zero_of_even_natCast_ne_zero hn hn_even)
  · rw [if_neg hn_even]
    have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
    calc
      Nat.card (TwoKernel (W := W) n) = Nat.card Unit :=
        Nat.card_congr (twoKernelOddEquiv (W := W) hn_odd)
      _ = 1 := by
        rw [Nat.card_eq_fintype_card]
        simp

private noncomputable def kernelSplitEquiv (n : ℕ) :
    {P : (W⁄k).Point // n • P = 0} ≃
      TwoKernel (W := W) n ⊕ NonTwoKernel (W := W) n where
  toFun P :=
    if h₂ : 2 • (P : (W⁄k).Point) = 0 then
      Sum.inl ⟨P.1, P.2, h₂⟩
    else
      Sum.inr ⟨P.1, P.2, h₂⟩
  invFun
    | Sum.inl P => ⟨P.1, P.2.1⟩
    | Sum.inr P => ⟨P.1, P.2.1⟩
  left_inv P := by
    by_cases h₂ : 2 • (P : (W⁄k).Point) = 0 <;> simp [h₂]
  right_inv P := by
    cases P with
    | inl P => simp [P.2.2]
    | inr P => simp [P.2.2]

private lemma torsion_card_arith {n : ℕ} (hn0 : n ≠ 0) :
    (if Even n then 4 else 1) +
        2 * ((n ^ 2 - if Even n then 4 else 1) / 2) = n ^ 2 := by
  by_cases hn_even : Even n
  · rcases hn_even with ⟨m, rfl⟩
    cases m with
    | zero => contradiction
    | succ a =>
      have he : Even ((a + 1) + (a + 1)) := ⟨a + 1, rfl⟩
      simp [he]
      have hc_le : 4 ≤ ((a + 1) + (a + 1)) ^ 2 := by nlinarith [Nat.zero_le a]
      have hdiv : 2 ∣ ((a + 1) + (a + 1)) ^ 2 - 4 := by
        have h_even_sq : 2 ∣ ((a + 1) + (a + 1)) ^ 2 := by
          use 2 * (a + 1) ^ 2
          ring
        exact Nat.dvd_sub h_even_sq (by norm_num : 2 ∣ 4)
      rw [Nat.mul_div_cancel' hdiv]
      exact Nat.add_sub_of_le hc_le
  · have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_even
    rcases hn_odd with ⟨m, rfl⟩
    have ho : ¬ Even (2 * m + 1) := Nat.not_even_two_mul_add_one m
    simp [ho]
    have hc_le : 1 ≤ (2 * m + 1) ^ 2 := by nlinarith [Nat.zero_le m]
    have hdiv : 2 ∣ (2 * m + 1) ^ 2 - 1 := by
      use 2 * m * (m + 1)
      rw [Nat.sub_eq_iff_eq_add hc_le]
      ring
    rw [Nat.mul_div_cancel' hdiv]
    exact Nat.add_sub_of_le hc_le

theorem nTorsion_card_eq [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (W.nTorsion n) = n ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by
    intro h0
    apply hn
    simp [h0]
  haveI : Finite (NonTwoKernel (W := W) n) :=
    Finite.of_equiv (Σ _x : (W.preΨ' n).rootSet k, Bool)
      (nonTwoKernelEquivRootBool (W := W) hn).symm
  haveI : Finite (TwoKernel (W := W) n) := by
    apply Nat.finite_of_card_ne_zero
    rw [twoKernel_card (W := W) hn]
    split_ifs <;> norm_num
  calc
    Nat.card (W.nTorsion n)
        = Nat.card {P : (W⁄k).Point // n • P = 0} :=
          Nat.card_congr (nTorsionEquivKernel (W := W) n)
    _ = Nat.card (TwoKernel (W := W) n ⊕ NonTwoKernel (W := W) n) :=
          Nat.card_congr (kernelSplitEquiv (W := W) n)
    _ = Nat.card (TwoKernel (W := W) n) + Nat.card (NonTwoKernel (W := W) n) := by
          rw [Nat.card_sum]
    _ = (if Even n then 4 else 1) +
          2 * ((n ^ 2 - if Even n then 4 else 1) / 2) := by
          rw [twoKernel_card (W := W) hn, nonTwoKernel_card (W := W) hn]
    _ = n ^ 2 := torsion_card_arith hn0

end KeystoneNTorsion

theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := by
  exact KeystoneNTorsion.nTorsion_card_eq (W := E) hn

private noncomputable def torsionByAddEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (d : ℕ) :
    Submodule.torsionBy ℤ G (d : ℤ) ≃+ Submodule.torsionBy ℤ H (d : ℤ) where
  toFun x := ⟨e x, by
    rw [Submodule.mem_torsionBy_iff]
    rw [← map_zsmul e (d : ℤ) (x : G)]
    simp [Submodule.smul_coe_torsionBy]⟩
  invFun y := ⟨e.symm y, by
    rw [Submodule.mem_torsionBy_iff]
    rw [← map_zsmul e.symm (d : ℤ) (y : H)]
    simp [Submodule.smul_coe_torsionBy]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

private noncomputable def torsionByPiAddEquiv {ι : Type*} {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] (d : ℕ) :
    Submodule.torsionBy ℤ ((i : ι) → G i) (d : ℤ) ≃+
      ((i : ι) → Submodule.torsionBy ℤ (G i) (d : ℤ)) where
  toFun x i := ⟨(x : (i : ι) → G i) i, by
    rw [Submodule.mem_torsionBy_iff]
    have hx := Submodule.smul_coe_torsionBy (R := ℤ) (M := ((i : ι) → G i))
      (a := (d : ℤ)) x
    exact congrFun hx i⟩
  invFun y := ⟨fun i => (y i : G i), by
    rw [Submodule.mem_torsionBy_iff]
    ext i
    exact Submodule.smul_coe_torsionBy (R := ℤ) (M := G i) (a := (d : ℤ)) (y i)⟩
  left_inv x := by ext i; rfl
  right_inv y := by ext i; rfl
  map_add' x y := by ext i; rfl

private noncomputable def torsionOfTorsionEquiv {A : Type*} [AddCommGroup A] {d n : ℕ}
    (hdn : d ∣ n) :
    Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A (n : ℤ)) (d : ℤ) ≃+
      Submodule.torsionBy ℤ A (d : ℤ) where
  toFun x := ⟨((x : Submodule.torsionBy ℤ A (n : ℤ)) : A), by
    rw [Submodule.mem_torsionBy_iff]
    have hx := Submodule.smul_coe_torsionBy (R := ℤ)
      (M := Submodule.torsionBy ℤ A (n : ℤ)) (a := (d : ℤ)) x
    exact congrArg Subtype.val hx⟩
  invFun y :=
    let hz : (d : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hdn
    ⟨⟨(y : A), Submodule.torsionBy_le_torsionBy_of_dvd (R := ℤ) (M := A)
      (d : ℤ) (n : ℤ) hz y.property⟩, by
      rw [Submodule.mem_torsionBy_iff]
      apply Subtype.ext
      exact Submodule.smul_coe_torsionBy (R := ℤ) (M := A) (a := (d : ℤ)) y⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl

private lemma zmod_prime_torsion_card {m p : ℕ} (hm0 : m ≠ 0) (hpm : p ∣ m) :
    Nat.card (Submodule.torsionBy ℤ (ZMod m) (p : ℤ)) = p := by
  classical
  haveI : NeZero m := ⟨hm0⟩
  change Nat.card (AddSubgroup.torsionBy (ZMod m) (p : ℤ)) = p
  have hker : AddSubgroup.torsionBy (ZMod m) (p : ℤ) =
      (nsmulAddMonoidHom p : ZMod m →+ ZMod m).ker := by
    ext x
    simp [AddMonoidHom.mem_ker]
  calc
    Nat.card (AddSubgroup.torsionBy (ZMod m) (p : ℤ))
        = Nat.card ((nsmulAddMonoidHom p : ZMod m →+ ZMod m).ker) := by rw [hker]
    _ = (Nat.card (ZMod m)).gcd p := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) p
    _ = m.gcd p := by rw [Nat.card_zmod]
    _ = p := Nat.gcd_eq_right hpm

private lemma pi_zmod_prime_torsion_card {ι : Type*} [Fintype ι] {m : ι → ℕ} {p : ℕ}
    (hm0 : ∀ i, m i ≠ 0) (hpm : ∀ i, p ∣ m i) :
    Nat.card (Submodule.torsionBy ℤ ((i : ι) → ZMod (m i)) (p : ℤ)) =
      p ^ Fintype.card ι := by
  classical
  haveI (i : ι) : NeZero (m i) := ⟨hm0 i⟩
  calc
    Nat.card (Submodule.torsionBy ℤ ((i : ι) → ZMod (m i)) (p : ℤ))
        = Nat.card ((i : ι) → Submodule.torsionBy ℤ (ZMod (m i)) (p : ℤ)) :=
          Nat.card_congr (torsionByPiAddEquiv (G := fun i => ZMod (m i)) p).toEquiv
    _ = ∏ i, Nat.card (Submodule.torsionBy ℤ (ZMod (m i)) (p : ℤ)) := by
          rw [Nat.card_pi]
    _ = ∏ _i : ι, p := by
          apply Finset.prod_congr rfl
          intro i _hi
          exact zmod_prime_torsion_card (hm0 i) (hpm i)
    _ = p ^ Fintype.card ι := by simp

private lemma pi_zmod_card {ι : Type*} [Fintype ι] {m : ι → ℕ} (hm0 : ∀ i, m i ≠ 0) :
    Nat.card ((i : ι) → ZMod (m i)) = ∏ i, m i := by
  classical
  haveI (i : ι) : NeZero (m i) := ⟨hm0 i⟩
  rw [Nat.card_pi]
  simp

private noncomputable def piCommAddEquiv {ι κ : Type*} {G : ι → Type*}
    [∀ i, Add (G i)] :
    ((i : ι) → κ → G i) ≃+ (κ → (i : ι) → G i) where
  toFun x j i := x i j
  invFun x i j := x j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    ext j i
    rfl

private lemma prime_power_torsion_equiv {A : Type*} [AddCommGroup A] {p a r : ℕ}
    (hp : Nat.Prime p) (ha : 0 < a)
    (h1 : Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) = p ^ r)
    (hpa : Nat.card (Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)) = (p ^ a) ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)) ≃+
      (Fin r → ZMod (p ^ a))) := by
  classical
  let G := Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)
  have hpowa_pos : 0 < p ^ a := pow_pos hp.pos a
  haveI : Finite G := Nat.finite_of_card_ne_zero (by
    change Nat.card (Submodule.torsionBy ℤ A ((p ^ a : ℕ) : ℤ)) ≠ 0
    rw [hpa]
    exact (pow_pos hpowa_pos r).ne')
  obtain ⟨ι, hι, m, hmgt, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  letI : Fintype ι := hι
  have hm0 : ∀ i, m i ≠ 0 := fun i => ne_of_gt ((zero_lt_one).trans (hmgt i))
  haveI (i : ι) : NeZero (m i) := ⟨hm0 i⟩
  let H := ⨁ i : ι, ZMod (m i)
  have hkillH_nat : ∀ y : H, (p ^ a) • y = 0 := by
    intro y
    have hx := Submodule.smul_torsionBy (R := ℤ) (M := A)
      (a := ((p ^ a : ℕ) : ℤ)) (e.symm y)
    have hy_int : (((p ^ a : ℕ) : ℤ) • y = 0) := by
      calc
        ((p ^ a : ℕ) : ℤ) • y = e (((p ^ a : ℕ) : ℤ) • e.symm y) := by
          rw [map_zsmul, e.apply_symm_apply]
        _ = 0 := by rw [hx, map_zero]
    rw [← natCast_zsmul y (p ^ a)]
    exact hy_int
  have hmdiv : ∀ i, m i ∣ p ^ a := by
    intro i
    have hof : (DirectSum.of (fun i : ι => ZMod (m i)) i) ((p ^ a) •
        (1 : ZMod (m i))) = 0 := by
      rw [map_nsmul]
      exact hkillH_nat (DirectSum.of (fun i : ι => ZMod (m i)) i (1 : ZMod (m i)))
    have hcoord : (p ^ a) • (1 : ZMod (m i)) = 0 := by
      have h := congrArg (fun z : H => z i) hof
      simpa [H, DirectSum.of_eq_same] using h
    simpa [ZMod.addOrderOf_one] using
      (addOrderOf_dvd_iff_nsmul_eq_zero (x := (1 : ZMod (m i))) (n := p ^ a)).mpr hcoord
  have hp_dvd_m : ∀ i, p ∣ m i := by
    intro i
    obtain ⟨k, _hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).1 (hmdiv i)
    rw [hk_eq]
    apply dvd_pow_self
    intro hk0
    have hmi1 : m i = 1 := by simpa [hk0] using hk_eq
    exact (ne_of_gt (hmgt i)) hmi1
  have hcard_torsion_H :
      Nat.card (Submodule.torsionBy ℤ H (p : ℤ)) = p ^ Fintype.card ι := by
    calc
      Nat.card (Submodule.torsionBy ℤ H (p : ℤ))
          = Nat.card (Submodule.torsionBy ℤ ((i : ι) → ZMod (m i)) (p : ℤ)) :=
            Nat.card_congr (torsionByAddEquiv
              (DirectSum.addEquivProd (fun i : ι => ZMod (m i))) p).toEquiv
      _ = p ^ Fintype.card ι := pi_zmod_prime_torsion_card hm0 hp_dvd_m
  have hcardι : Fintype.card ι = r := by
    apply Nat.pow_right_injective hp.two_le
    calc
      p ^ Fintype.card ι = Nat.card (Submodule.torsionBy ℤ H (p : ℤ)) :=
        hcard_torsion_H.symm
      _ = Nat.card (Submodule.torsionBy ℤ G (p : ℤ)) :=
          (Nat.card_congr (torsionByAddEquiv e p).toEquiv).symm
      _ = Nat.card (Submodule.torsionBy ℤ A (p : ℤ)) :=
          Nat.card_congr (torsionOfTorsionEquiv (A := A) (d := p) (n := p ^ a)
            (dvd_pow_self p ha.ne')).toEquiv
      _ = p ^ r := h1
  have hprod : ∏ i, m i = (p ^ a) ^ r := by
    calc
      ∏ i, m i = Nat.card ((i : ι) → ZMod (m i)) := (pi_zmod_card hm0).symm
      _ = Nat.card H :=
          (Nat.card_congr (DirectSum.addEquivProd (fun i : ι => ZMod (m i))).toEquiv).symm
      _ = Nat.card G := (Nat.card_congr e.toEquiv).symm
      _ = (p ^ a) ^ r := hpa
  have hprod_const : (∏ i, m i) = ∏ _i : ι, p ^ a := by
    rw [hprod, Finset.prod_const, Finset.card_univ, hcardι]
  have hm_eq : ∀ i, m i = p ^ a := by
    intro i
    apply le_antisymm
    · exact Nat.le_of_dvd hpowa_pos (hmdiv i)
    · by_contra hnot
      have hlt : m i < p ^ a := lt_of_not_ge hnot
      have hprod_lt : (∏ j, m j) < ∏ _j : ι, p ^ a := by
        exact Finset.prod_lt_prod (s := Finset.univ)
          (fun j _ => (zero_lt_one).trans (hmgt j))
          (fun j _ => Nat.le_of_dvd hpowa_pos (hmdiv j))
          ⟨i, Finset.mem_univ i, hlt⟩
      rw [hprod_const] at hprod_lt
      exact (lt_irrefl _) hprod_lt
  let e_m : ((i : ι) → ZMod (m i)) ≃+ ((i : ι) → ZMod (p ^ a)) :=
    AddEquiv.piCongrRight fun i => (ZMod.ringEquivCongr (hm_eq i)).toAddEquiv
  let e_idx : ((i : ι) → ZMod (p ^ a)) ≃+ (Fin r → ZMod (p ^ a)) :=
    { Equiv.piCongrLeft (fun _ : Fin r => ZMod (p ^ a)) (Fintype.equivFinOfCardEq hcardι) with
      map_add' := by
        intro x y
        ext j
        simp [Equiv.piCongrLeft] }
  exact ⟨e.trans <| (DirectSum.addEquivProd (fun i : ι => ZMod (m i))).trans <|
    e_m.trans e_idx⟩

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  classical
  by_cases hn1 : n = 1
  · subst n
    haveI : Unique (Submodule.torsionBy ℤ A (1 : ℤ)) := {
      default := 0
      uniq := by
        intro x
        ext
        have hx0 : (x : A) ∈ (⊥ : Submodule ℤ A) := by
          simpa [Submodule.torsionBy_one] using x.property
        simpa using hx0 }
    haveI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff).2 rfl
    exact ⟨AddEquiv.ofUnique⟩
  let ι := {p : ℕ // p ∈ n.primeFactors}
  let q : ι → ℕ := fun p => p.1 ^ n.factorization p.1
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hp : ∀ p : ι, Nat.Prime p.1 := fun p => Nat.prime_of_mem_primeFactors p.2
  have hpdvd : ∀ p : ι, p.1 ∣ n := fun p => (Nat.mem_primeFactors.mp p.2).2.1
  have hfac_pos : ∀ p : ι, 0 < n.factorization p.1 := fun p =>
    (hp p).factorization_pos_of_dvd hn0 (hpdvd p)
  have hq_dvd : ∀ p : ι, q p ∣ n := by
    intro p
    exact ((hp p).pow_dvd_iff_le_factorization hn0).mpr le_rfl
  have hcomponent :
      ∀ p : ι, Nonempty (Submodule.torsionBy ℤ A (q p : ℤ) ≃+
        (Fin r → ZMod (q p))) := by
    intro p
    apply prime_power_torsion_equiv (hp p) (hfac_pos p)
    · simpa using h p.1 (hpdvd p)
    · simpa [q] using h (q p) (hq_dvd p)
  let G := Submodule.torsionBy ℤ A (n : ℤ)
  have hprod_nat : ∏ p : ι, q p = n := by
    simpa [ι, q] using (Nat.prod_pow_primeFactors_factorization hn0).symm
  have hprod_int : ∏ p : ι, (q p : ℤ) = (n : ℤ) := by
    exact_mod_cast hprod_nat
  have hcop :
      ((Finset.univ : Finset ι) : Set ι).Pairwise
        (Function.onFun IsCoprime fun p : ι => (q p : ℤ)) := by
    intro p _hpmem q' _hqmem hpq
    have hpq_ne : p.1 ≠ q'.1 := by
      intro hval
      exact hpq (Subtype.ext hval)
    exact (Nat.coprime_pow_primes (n.factorization p.1) (n.factorization q'.1)
      (hp p) (hp q') hpq_ne).isCoprime
  have htorsion :
      Module.IsTorsionBy ℤ G (∏ p ∈ (Finset.univ : Finset ι), (q p : ℤ)) := by
    intro x
    have hprod_int' : (∏ p ∈ (Finset.univ : Finset ι), (q p : ℤ)) = (n : ℤ) := by
      simpa using hprod_int
    rw [hprod_int']
    apply Subtype.ext
    exact Submodule.smul_coe_torsionBy (R := ℤ) (M := A) (a := (n : ℤ)) x
  have hinternal := Submodule.torsionBy_isInternal (R := ℤ) (M := G)
    (S := (Finset.univ : Finset ι)) (q := fun p : ι => (q p : ℤ)) hcop htorsion
  let σ := (Finset.univ : Finset ι)
  let decomp : G ≃+ ⨁ p : σ, Submodule.torsionBy ℤ G (q p.1 : ℤ) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap
      (fun p : σ => Submodule.torsionBy ℤ G (q p.1 : ℤ))) hinternal).symm.toAddEquiv
  let compEquiv : (p : σ) →
      Submodule.torsionBy ℤ G (q p.1 : ℤ) ≃+ (Fin r → ZMod (q p.1)) :=
    fun p => (torsionOfTorsionEquiv (A := A) (d := q p.1) (n := n) (hq_dvd p.1)).trans
      (hcomponent p.1).some
  let comps : (⨁ p : σ, Submodule.torsionBy ℤ G (q p.1 : ℤ)) ≃+
      ⨁ p : σ, (Fin r → ZMod (q p.1)) :=
    DFinsupp.mapRange.addEquiv compEquiv
  let prodEquiv : (⨁ p : σ, (Fin r → ZMod (q p.1))) ≃+
      ((p : σ) → Fin r → ZMod (q p.1)) :=
    DirectSum.addEquivProd (fun p : σ => Fin r → ZMod (q p.1))
  let univEquiv : σ ≃ ι := Equiv.subtypeUnivEquiv (fun _ => Finset.mem_univ _)
  let reindex : ((p : σ) → Fin r → ZMod (q p.1)) ≃+
      ((p : ι) → Fin r → ZMod (q p)) :=
    { toFun := fun x p => x (univEquiv.symm p)
      invFun := fun x p => x (univEquiv p)
      left_inv := by
        intro x
        ext p j
        rfl
      right_inv := by
        intro x
        ext p j
        rfl
      map_add' := by
        intro x y
        ext p j
        rfl }
  let swap : ((p : ι) → Fin r → ZMod (q p)) ≃+
      (Fin r → (p : ι) → ZMod (q p)) :=
    piCommAddEquiv
  let crt : (Fin r → (p : ι) → ZMod (q p)) ≃+ (Fin r → ZMod n) :=
    AddEquiv.piCongrRight fun _ =>
      (ZMod.equivPi n hn0).symm.toAddEquiv
  exact ⟨decomp.trans <| comps.trans <| prodEquiv.trans <| reindex.trans <| swap.trans crt⟩

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

namespace AddEquiv

/-- Any additive equivalence between `ZMod n`-modules is automatically `ZMod n`-linear. -/
def toZModLinearEquiv
    {n : ℕ} {A B : Type*}
    [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod n) A] [Module (ZMod n) B]
    (e : A ≃+ B) :
    A ≃ₗ[ZMod n] B where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := by
    intro c x
    exact ZMod.map_smul e.toAddMonoidHom c x

end AddEquiv

/--
The geometric `n`-torsion over a separably closed field is linearly equivalent to
the rank-two coordinate module over `ZMod n`.
-/
theorem WeierstrassCurve.geomNTorsion_rank_two_linear
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n)) := by
  obtain ⟨eProd⟩ := E.n_torsion_dimension hn
  let ePi : E.nTorsion n ≃+ (Fin 2 → ZMod n) :=
    eProd.trans (RingEquiv.piFinTwo (fun _ : Fin 2 => ZMod n)).symm.toAddEquiv
  exact ⟨ePi.toZModLinearEquiv (n := n)⟩

/-- A basis of geometric `n`-torsion over `ZMod n`, indexed by `Fin 2`. -/
theorem WeierstrassCurve.geomNTorsion_basis
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) (ZMod n) (E.nTorsion n)) := by
  obtain ⟨e⟩ := E.geomNTorsion_rank_two_linear hn
  exact ⟨Module.Basis.ofEquivFun e⟩

/--
The rank-two linear structure on geometric torsion over the algebraic closure.
-/
theorem WeierstrassCurve.geomNTorsion_rank_two_linear_algClosure
    {K : Type u} [Field K] [DecidableEq K]
    [DecidableEq (AlgebraicClosure K)]
    (E : WeierstrassCurve K) [E.IsElliptic]
    {n : ℕ} (hn : (n : AlgebraicClosure K) ≠ 0) :
    Nonempty
      (((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)
        ≃ₗ[ZMod n] (Fin 2 → ZMod n)) := by
  classical
  exact
    (E.map (algebraMap K (AlgebraicClosure K))).geomNTorsion_rank_two_linear hn

/-- A basis of geometric torsion over the algebraic closure. -/
theorem WeierstrassCurve.geomNTorsion_basis_algClosure
    {K : Type u} [Field K] [DecidableEq K]
    [DecidableEq (AlgebraicClosure K)]
    (E : WeierstrassCurve K) [E.IsElliptic]
    {n : ℕ} (hn : (n : AlgebraicClosure K) ≠ 0) :
    Nonempty
      (Module.Basis (Fin 2) (ZMod n)
        ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)) := by
  classical
  obtain ⟨e⟩ := E.geomNTorsion_rank_two_linear_algClosure hn
  exact ⟨Module.Basis.ofEquivFun e⟩

-- follows easily from the above
noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := sorry

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul P := by
        change Points.map E ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) P = P
        rw [show ((1 : K ≃ₐ[k] K) : K →ₐ[k] K) = AlgHom.id k K from rfl]
        simp [Points.map_id]
      mul_smul g h P := by
        change Points.map E ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) P =
          Points.map E (g : K →ₐ[k] K) (Points.map E (h : K →ₐ[k] K) P)
        rw [show ((g * h : K ≃ₐ[k] K) : K →ₐ[k] K) =
          (g : K →ₐ[k] K).comp h from rfl]
        have hcomp := Points.map_comp E K K K (h : K →ₐ[k] K) (g : K →ₐ[k] K)
        rw [← AddMonoidHom.comp_apply]
        congr 1
        exact hcomp.symm
      smul_zero g := by
        change Points.map E (g : K →ₐ[k] K) 0 = 0
        exact map_zero _
      smul_add g P Q := by
        change Points.map E (g : K →ₐ[k] K) (P + Q) =
          Points.map E (g : K →ₐ[k] K) P + Points.map E (g : K →ₐ[k] K) Q
        exact map_add _ P Q

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
