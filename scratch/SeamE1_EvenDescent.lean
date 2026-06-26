module

public import scratch.SeamE1_SeparabilityCore

/-! # Even-case EDS descent for separability

Proves that a divisor of a polynomial with no double roots itself has no double roots.
This is used to reduce the odd-n case to the even-n case:
since `preΨ'(n) | preΨ'(2n)`, rootwise separability of `preΨ'(2n)` implies that of `preΨ'(n)`.
-/

set_option maxHeartbeats 800000

@[expose] public section

open Polynomial

namespace WeierstrassCurve.SeparabilityDescent

variable {K : Type*} [Field K]

/-! ### Rootwise separability descent through divisibility -/

/-- At a root of `f`, if `f * g` has no double roots (derivative nonzero at every root),
then `f` has no double root there either. -/
theorem deriv_ne_zero_at_root_of_mul
    {f g : K[X]}
    (hfg : forall y : K, (f * g).IsRoot y -> Not ((derivative (f * g)).IsRoot y))
    {x : K} (hx : f.IsRoot x) :
    Not ((derivative f).IsRoot x) := by
  -- f(x) = 0 implies (f*g)(x) = 0
  have hfg_root : (f * g).IsRoot x := by
    simp only [IsRoot, eval_mul, mul_eq_zero]
    exact Or.inl (IsRoot.def.mp hx)
  -- So (f*g)'(x) != 0
  have hne := hfg x hfg_root
  -- (f*g)' = f'*g + f*g', and at x where f(x)=0: (f*g)'(x) = f'(x)*g(x)
  rw [derivative_mul] at hne
  intro hf_deriv
  apply hne
  simp only [IsRoot, eval_add, eval_mul]
  rw [IsRoot.def.mp hx, IsRoot.def.mp hf_deriv]
  ring

/-- Rootwise separability descends through the even factorization:
if `preΨ'(2k)` has no double roots and `k >= 3`,
then `preΨ'(k)` has no double roots. -/
theorem preΨ_deriv_ne_zero_of_double [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {k : ℕ}
    (hk_ge : k >= 3)
    (h2k_sep : forall x : K, (W.preΨ' (2 * k)).IsRoot x ->
      Not ((derivative (W.preΨ' (2 * k))).IsRoot x))
    {x : K} (hx : (W.preΨ' k).IsRoot x) :
    Not ((derivative (W.preΨ' k)).IsRoot x) := by
  -- Write k = m + 3
  set m := k - 3
  have hk_eq : k = m + 3 := by omega
  -- Suffices to show for preΨ'(m+3) since k = m+3
  suffices h : Not ((derivative (W.preΨ' (m + 3))).IsRoot x) by rwa [hk_eq]
  have hx' : (W.preΨ' (m + 3)).IsRoot x := by rwa [hk_eq] at hx
  -- The even factorization: preΨ'(2*(m+3)) = preΨ'(m+3) * cofactor
  have hfact := SeparabilityCore.preΨ'_even_factor W m
  -- Rewrite the separability hypothesis using the factorization
  set cof := W.preΨ' (m + 2) ^ 2 * W.preΨ' (m + 5) -
    W.preΨ' (m + 1) * W.preΨ' (m + 4) ^ 2 with cof_def
  have h_sep : forall y : K, (W.preΨ' (m + 3) * cof).IsRoot y ->
      Not ((derivative (W.preΨ' (m + 3) * cof)).IsRoot y) := by
    intro y hy hdy
    have h2k_rw : 2 * k = 2 * (m + 3) := by omega
    exact h2k_sep y (by rwa [h2k_rw, hfact]) (by rwa [h2k_rw, hfact])
  exact deriv_ne_zero_at_root_of_mul h_sep hx'

end WeierstrassCurve.SeparabilityDescent
