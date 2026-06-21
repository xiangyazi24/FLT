/-
KEYSTONE build: n_torsion_card = n² over a sep-closed field, MODULO two named seams.
SEAM 1 = preΨ'_separable (étaleness of [n]); SEAM 2 = xRep coordinate formula.
Both requested seams are stated as named `sorry` lemmas — NO new axioms. Two additional
bookkeeping/geometric gaps are named explicitly below and should be discharged next.
Reference design: scratch/Keystone_MasterDesign.md (the CORE 1 decomposition, lemmas A–E).
#print axioms must show NO custom axiom (sorryAx from the named gaps is expected).
-/
import Mathlib
import FLT.EllipticCurve.Torsion

open WeierstrassCurve Polynomial
open WeierstrassCurve.Affine

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
    (W.preΨ' n).Separable := sorry

/-- SEAM 2 (x-coordinate division polynomial formula), stated in the direct form needed for
kernel membership. This is the `xRep_zsmul_some_eq_divisionPolynomial` seam after extracting the
zero-denominator criterion. -/
theorem nsmul_eq_zero_iff_ΨSq_eval {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := sorry

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

lemma nonTwoKernel_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
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

theorem twoTorsionKernel_card [IsSepClosed k] (h₂ : (2 : k) ≠ 0) :
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

lemma twoKernel_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
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
