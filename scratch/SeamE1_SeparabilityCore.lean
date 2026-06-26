module

public import scratch.KeystoneSeparability
public import scratch.KeystoneCoprimality
public import scratch.Bridge1Even
public import scratch.SeamE1_PolySeparability
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # SEAM1 — Core separability: preΨ'(n) is separable when (n:K) ≠ 0

Proves the **rootwise separability** of the reduced n-division polynomial
`preΨ' n` for elliptic curves: at any root `x` of `preΨ' n` over an algebraically
closed field with `(n : K) ≠ 0`, the derivative `(preΨ' n)'(x) ≠ 0`.

## Approach

Strong induction on n via the EDS even recurrence:
- Base cases: n ≤ 3 (vacuous or Bezout certificate for n=3)
- Even n = 2*(m+3) ≥ 6: factorization `preΨ'(2k) = preΨ'(k) · cofactor`,
  at a root of preΨ'(k), the derivative factors as `(preΨ'(k))' · cofactor`,
  with both factors nonzero (by IH and evenCofactor_ne_zero). -/

set_option maxHeartbeats 6400000

@[expose] public section

open Polynomial WeierstrassCurve FLT.EDS

namespace WeierstrassCurve.SeparabilityCore

variable {K : Type*} [Field K]

/-- A separable polynomial has no root in common with its derivative. -/
theorem eval_deriv_ne_zero_of_separable {f : K[X]} (hf : f.Separable) {x : K}
    (hroot : f.IsRoot x) : ¬ (derivative f).IsRoot x := by
  rw [Polynomial.separable_def] at hf
  obtain ⟨a, b, hab⟩ := hf
  intro hderiv
  have : eval x (a * f + b * derivative f) = eval x 1 := by rw [hab]
  simp only [eval_add, eval_mul, eval_one, IsRoot.def.mp hroot,
    IsRoot.def.mp hderiv, mul_zero, add_zero] at this
  exact absurd this.symm one_ne_zero

/-- n = 3: Bezout certificate. -/
private theorem case_n3 (W : WeierstrassCurve K) [W.IsElliptic]
    (h3 : (3 : K) ≠ 0) {x : K}
    (hx : (W.preΨ' 3).IsRoot x) :
    ¬ (derivative (W.preΨ' 3)).IsRoot x := by
  rw [preΨ'_three] at hx ⊢
  exact eval_deriv_ne_zero_of_separable (Psi3_separable W h3) hx

/-! ### Even-case EDS descent infrastructure -/

public lemma preΨ'_even_factor (W : WeierstrassCurve K) (m : ℕ) :
    W.preΨ' (2 * (m + 3)) = W.preΨ' (m + 3) *
      (W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 5) -
       W.preΨ' (m + 1) * W.preΨ' (m + 4) ^ 2) := by
  rw [preΨ'_even]; ring

public lemma deriv_preΨ'_even_at_half_root (W : WeierstrassCurve K) (m : ℕ) {x : K}
    (hroot : (W.preΨ' (m + 3)).IsRoot x) :
    (derivative (W.preΨ' (2 * (m + 3)))).eval x =
      (derivative (W.preΨ' (m + 3))).eval x *
      (W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 5) -
       W.preΨ' (m + 1) * W.preΨ' (m + 4) ^ 2).eval x := by
  have hfact := preΨ'_even_factor W m
  conv_lhs => rw [hfact, derivative_mul]
  simp only [eval_add, eval_mul]
  rw [IsRoot.def.mp hroot, zero_mul, add_zero]

public lemma preΨ'_adjacent_ne_zero_at_half_root
    (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ) {x : K}
    (h4 : (4 : K) ≠ 0)
    (hx_root_k : (W.preΨ' (m + 3)).IsRoot x) :
    (W.preΨ' (m + 2)).eval x ≠ 0 ∧ (W.preΨ' (m + 4)).eval x ≠ 0 := by
  have hk : (W.preΨ' (m + 3)).eval x = 0 := IsRoot.def.mp hx_root_k
  constructor
  · intro ha0
    apply no_adjacent_preΨ_zero W x h4 (↑(m + 2))
    refine ⟨?_, ?_⟩
    · change (W.preΨ (↑(m + 2))).eval x = 0; rw [preΨ_ofNat]; exact ha0
    · change (W.preΨ (↑(m + 2) + 1)).eval x = 0
      rw [show (↑(m + 2) : ℤ) + 1 = ↑(m + 3) from by push_cast; ring, preΨ_ofNat]; exact hk
  · intro hb0
    apply no_adjacent_preΨ_zero W x h4 (↑(m + 3))
    refine ⟨?_, ?_⟩
    · change (W.preΨ (↑(m + 3))).eval x = 0; rw [preΨ_ofNat]; exact hk
    · change (W.preΨ (↑(m + 3) + 1)).eval x = 0
      rw [show (↑(m + 3) : ℤ) + 1 = ↑(m + 4) from by push_cast; ring, preΨ_ofNat]; exact hb0

/-! ### Strong induction helpers -/

private lemma four_ne_of_two (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  intro h4; apply h2
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this] at h4; exact (mul_eq_zero.mp h4).elim id id

private lemma pe_nat (W : WeierstrassCurve K) (x : K) (n : ℕ) :
    pe W x (↑n) = (W.preΨ' n).eval x := by
  simp [pe, preΨ_ofNat]

/-- Cofactor nonvanishing at roots of preΨ'(m+3), Ψ₃ ≠ 0 case with m ≥ 1. -/
private theorem cof_ne_Psi3_ne
    (W : WeierstrassCurve K) [W.IsElliptic]
    (h4 : (4 : K) ≠ 0) (h2 : (2 : K) ≠ 0)
    {m : ℕ} (hm : m ≥ 1) {x : K}
    (hroot : pe W x (↑(m + 3)) = 0)
    (hΨ₂ : sx W x ≠ 0) (hΨ₃ : c3x W x ≠ 0) :
    pe W x (↑(m + 2)) ^ 2 * pe W x (↑(m + 5)) -
     pe W x (↑(m + 1)) * pe W x (↑(m + 4)) ^ 2 ≠ 0 := by
  have hk_ge : (4 : ℤ) ≤ ↑(m + 3) := by push_cast; omega
  have e1 : (↑(m + 2) : ℤ) = ↑(m + 3) - 1 := by push_cast; ring
  have e2 : (↑(m + 1) : ℤ) = ↑(m + 3) - 2 := by push_cast; ring
  have e4 : (↑(m + 4) : ℤ) = ↑(m + 3) + 1 := by push_cast; ring
  have e5 : (↑(m + 5) : ℤ) = ↑(m + 3) + 2 := by push_cast; ring
  rw [e1, e2, e4, e5]
  exact PolySep.evenCofactor_ne_zero_Psi3_ne W h4 h2 hk_ge hroot hΨ₂ hΨ₃

/-- Cofactor nonvanishing at roots of preΨ'(m+3), both Ψ₃ strata. -/
private theorem cofactor_ne_at_half_root
    (W : WeierstrassCurve K) [W.IsElliptic]
    (h4 : (4 : K) ≠ 0) (h2 : (2 : K) ≠ 0)
    {m : ℕ} {x : K}
    (hn : (2 * ((m : K) + 3)) ≠ 0)
    (hroot_k : pe W x (↑(m + 3)) = 0)
    (hroot_n : (W.preΨ' (2 * (m + 3))).IsRoot x) :
    pe W x (↑(m + 2)) ^ 2 * pe W x (↑(m + 5)) -
     pe W x (↑(m + 1)) * pe W x (↑(m + 4)) ^ 2 ≠ 0 := by
  have hΨ₂ : sx W x ≠ 0 := by
    rw [sx]
    have hn' : ((2 * (m + 3) : ℕ) : K) ≠ 0 := by push_cast; exact hn
    exact preΨ'_root_Ψ₂Sq_ne' W hn' hroot_n
  by_cases hΨ₃ : c3x W x = 0
  · -- Ψ₃ = 0 stratum: rank-3 apparition + Somos analysis
    sorry
  · by_cases hm : m = 0
    · subst hm; rw [pe_nat] at hroot_k; simp at hroot_k; exact absurd hroot_k hΨ₃
    · exact cof_ne_Psi3_ne W h4 h2 (by omega) hroot_k hΨ₂ hΨ₃

/-! ### The predicate for strong induction -/

private def RootSepPred (W : WeierstrassCurve K) [IsAlgClosed K] [W.IsElliptic] (n : ℕ) : Prop :=
  (n : K) ≠ 0 → ∀ x : K, (W.preΨ' n).IsRoot x → ¬ (derivative (W.preΨ' n)).IsRoot x

/-- Even step for n = 2*(m+3). -/
private theorem even_step [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {m : ℕ}
    (hn : (2 * ((m : K) + 3)) ≠ 0)
    (ih : ∀ k : ℕ, k < 2 * (m + 3) → RootSepPred W k)
    {x : K}
    (hx : (W.preΨ' (2 * (m + 3))).IsRoot x) :
    ¬ (derivative (W.preΨ' (2 * (m + 3)))).IsRoot x := by
  have h2_ne : (2 : K) ≠ 0 := left_ne_zero_of_mul hn
  have hk_ne : (m : K) + 3 ≠ 0 := right_ne_zero_of_mul hn
  have h4_ne : (4 : K) ≠ 0 := four_ne_of_two h2_ne
  have hfact := preΨ'_even_factor W m
  have hprod : (W.preΨ' (m + 3)).eval x *
    (W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 5) -
     W.preΨ' (m + 1) * W.preΨ' (m + 4) ^ 2).eval x = 0 := by
    rw [← eval_mul, ← hfact]; exact IsRoot.def.mp hx
  rcases mul_eq_zero.mp hprod with hk_root | hcof_root
  · -- Case A: preΨ'(m+3)(x) = 0
    have hk_lt : m + 3 < 2 * (m + 3) := by omega
    have hk_ne' : ((m + 3 : ℕ) : K) ≠ 0 := by push_cast; exact hk_ne
    have hk_sep := ih (m + 3) hk_lt hk_ne' x (IsRoot.def.mpr hk_root)
    have hpe_root : pe W x (↑(m + 3)) = 0 := by rw [pe_nat]; exact hk_root
    have hcof_ne := cofactor_ne_at_half_root W h4_ne h2_ne hn hpe_root hx
    intro hderiv
    rw [hfact, derivative_mul, IsRoot, eval_add, eval_mul, eval_mul,
        hk_root, zero_mul, add_zero] at hderiv
    rcases mul_eq_zero.mp hderiv with hd | hc
    · exact hk_sep (IsRoot.def.mpr hd)
    · rw [pe_nat, pe_nat, pe_nat, pe_nat] at hcof_ne
      exact hcof_ne (by simp only [eval_sub, eval_mul, eval_pow] at hc ⊢; exact hc)
  · -- Case B: cofactor(x) = 0, preΨ'(m+3)(x) ≠ 0
    sorry

/-- **Main theorem**: rootwise separability of preΨ'(n).

At any root of `preΨ' n` over an algebraically closed field with `(n:K) ≠ 0`
and an elliptic curve, the derivative does not vanish. -/
public theorem preΨ'_deriv_ne_zero_at_root_general [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x := by
  suffices ∀ n, @RootSepPred K _ W _ _ n from this n hn x hx
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro hn' x' hx'
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · simp at hn'
    · simp [IsRoot] at hx'
    · simp [IsRoot] at hx'
    · have h3 : (3 : K) ≠ 0 := by exact_mod_cast hn'
      exact case_n3 W h3 hx'
  · rcases Nat.even_or_odd n with heven | hodd
    · obtain ⟨j, hj⟩ := heven
      rcases Nat.lt_or_ge j 3 with hj_lt | hj_ge
      · -- j < 3 and n ≥ 4: j = 2, n = 4
        have : j = 2 := by omega
        subst this
        -- n = 4: TODO base case via Bezout certificate
        sorry
      · -- j ≥ 3: n = 2*(m+3)
        have hn_eq : n = 2 * ((j - 3) + 3) := by omega
        have hn' : (2 * (((j - 3 : ℕ) : K) + 3)) ≠ 0 := by
          intro h0; apply hn'
          have : (n : K) = 2 * (((j - 3 : ℕ) : K) + 3) := by
            push_cast; push_cast [hn_eq]; ring
          rw [this]; exact h0
        rw [hn_eq] at hx' ⊢
        exact even_step W hn' (fun k hk => ih k (by rw [hn_eq]; exact hk)) hx'
    · -- n is odd
      sorry

end WeierstrassCurve.SeparabilityCore
