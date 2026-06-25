module

public import scratch.KeystoneSeparability
public import scratch.KeystoneCoprimality
public import scratch.Bridge1Even
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # SEAM1 — Core separability: preΨ'(n) is separable when (n:K) ≠ 0

Proves the **rootwise separability** of the reduced n-division polynomial
`preΨ' n` for elliptic curves: at any root `x` of `preΨ' n` over an algebraically
closed field with `(n : K) ≠ 0`, the derivative `(preΨ' n)'(x) ≠ 0`.

This is the mathematical heart of SEAM1. The approach combines:
- Bezout certificates for small n (n = 3)
- EDS (Elliptic Divisibility Sequence) recurrence descent for general n

## Proven infrastructure (0 sorry)

- `eval_deriv_ne_zero_of_separable` — separable ⟹ no common root with derivative
- `case_n3` — n = 3 by Bezout certificate
- `preΨ'_even_factor` — `preΨ'(2*(m+3)) = preΨ'(m+3) · cofactor`
- `deriv_preΨ'_even_at_half_root` — product rule at half-index root

## Remaining sorry (1)

The n ≥ 4 case of `preΨ'_deriv_ne_zero_at_root_general`. The even-case descent
machinery is complete: once `evenCofactor_eval_ne_zero` is proven, the even case
closes. The odd case requires either a parallel descent or reduction to the even
case via `preΨ'(2n) = preΨ'(n) · cofactor`.

See `SeamE1_Core.lean` for how this is used to close `dual_root_implies_tangent_zero`. -/

set_option maxHeartbeats 1600000

@[expose] public section

open Polynomial

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

/-- n = 3: Bezout certificate (0 sorry, 0 axiom). -/
private theorem case_n3 (W : WeierstrassCurve K) [W.IsElliptic]
    (h3 : (3 : K) ≠ 0) {x : K}
    (hx : (W.preΨ' 3).IsRoot x) :
    ¬ (derivative (W.preΨ' 3)).IsRoot x := by
  rw [preΨ'_three] at hx ⊢
  exact eval_deriv_ne_zero_of_separable (Psi3_separable W h3) hx

/-! ### Even-case EDS descent infrastructure -/

/-- The EDS even factorization: `preΨ'(2*(m+3)) = preΨ'(m+3) · cofactor`.

This follows directly from the EDS even recurrence `preΨ'_even`, which gives
`preΨ'(2*(m+3)) = preΨ'(m+2)² · preΨ'(m+3) · preΨ'(m+5) - preΨ'(m+1) · preΨ'(m+3) · preΨ'(m+4)²`
and factoring out `preΨ'(m+3)`. -/
public lemma preΨ'_even_factor (W : WeierstrassCurve K) (m : ℕ) :
    W.preΨ' (2 * (m + 3)) = W.preΨ' (m + 3) *
      (W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 5) -
       W.preΨ' (m + 1) * W.preΨ' (m + 4) ^ 2) := by
  rw [preΨ'_even]; ring

/-- At a root of `preΨ'(m+3)`, the derivative of `preΨ'(2*(m+3))` factors through
    the cofactor via the Leibniz rule: the `preΨ'(m+3) · cof'` term vanishes since
    `preΨ'(m+3)(x) = 0`. -/
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

/-- At a root x of preΨ'(2*(m+3)) where preΨ'(m+3)(x) = 0, the adjacent
    values pe(m+2)(x) and pe(m+4)(x) are both nonzero.

    This is a direct consequence of `no_adjacent_preΨ_zero` from
    KeystoneCoprimality. -/
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

/-- **Main theorem**: rootwise separability of preΨ'(n).

At any root of `preΨ' n` over an algebraically closed field with `(n:K) ≠ 0`
and an elliptic curve, the derivative does not vanish.

STATUS: n ≤ 3 complete. n ≥ 4 uses the EDS descent machinery above. -/
public theorem preΨ'_deriv_ne_zero_at_root_general [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x := by
  -- Handle small n cases first
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · -- n < 4: either vacuous (n ≤ 2) or Bezout (n = 3)
    have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · simp at hn
    · simp [IsRoot] at hx
    · simp [IsRoot] at hx
    · -- n = 3: Bezout certificate
      have h3 : (3 : K) ≠ 0 := by exact_mod_cast hn
      exact case_n3 W h3 hx
  · -- n ≥ 4: EDS descent argument
    -- The even-case descent machinery (preΨ'_even_factor, deriv_preΨ'_even_at_half_root,
    -- preΨ'_adjacent_ne_zero_at_half_root) is fully proven. What remains:
    -- 1. Prove the even cofactor is nonzero at roots of the half-index (CAS-verified:
    --    Res(Ψ₃, Ψ₂Sq²-preΨ₄) = 16·Δ⁴ ≠ 0, and the Somos relation forces 2α = 0
    --    when the cofactor vanishes with char K ≠ 2).
    -- 2. Handle the case where the root is NOT a root of the half-index (cofactor root).
    -- 3. Handle odd n via the EDS odd recurrence.
    -- 4. Handle n = 4, 5 base cases (n = 4: Res(preΨ₄, preΨ₄') = 512·Δ⁵ ≠ 0).
    sorry

end WeierstrassCurve.SeparabilityCore
