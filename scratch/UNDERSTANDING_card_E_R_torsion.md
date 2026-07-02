# card_E_R_torsion_le — Proof Design (Fable oracle, 2026-07-02)

## Target sorry

```lean
theorem card_E_R_torsion_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    Set.Finite {P : (E⁄ℝ).Point | (n : ℕ) • P = 0} ∧
      Set.ncard {P : (E⁄ℝ).Point | (n : ℕ) • P = 0} ≤ 2 * n
```

## Architecture

```
(E⁄ℝ).Point
  │ Point.map (algebraMap ℚ ℝ)     [Mathlib, injective]
  ▼
(E.map (algebraMap ℚ ℝ)).Point
  │ variableChangePoint (toShortNF)  [S0, injective, u=1]
  ▼
shortW(A,B).Point
  │ componentBitHom                  [S1-S3, surjective onto ZMod 2]
  ▼
ZMod 2       ker = E(ℝ)⁰ (identity component)
  │
  │ θ : ker → AddCircle(2T)         [S4-S8, injective AddMonoidHom]
  ▼
AddCircle(2T)
  │ card_torsion_le_of_isSMulRegular [Mathlib: |n-torsion| ≤ n]
  ▼
|E(ℝ)⁰[n]| ≤ n, then coset trick → |E(ℝ)[n]| ≤ 2n
```

## S0: Variable Change Point Hom (in progress)

Injective `AddMonoidHom` for u=1 VariableChange. ~200 lines.
- Point map: (x,y) ↦ (x-r, y-s(x-r)-t)
- Template: Mathlib's Point.map + baseChange_* formulas
- Key: equation_iff_nonsingular (Δ≠0) avoids separate Nonsingular transport

## S4: σ integral definition + basic properties

Define σ(x) = ∫_{Ioi x} dt/√f(t), NOT as ∫_e^x.

**Why σ, not τ:** τ(x) = ∫_e^x has T-jumps at O and (e,0) that don't vanish mod 2T.
σ measures from ∞, giving 2T-jumps only (killed by AddCircle).

Key facts:
- g(t) = (√f(t))⁻¹ (junk extension: f<0 → sqrt=0 → 0⁻¹=0)
- σ(x) = ∫_{Ioi x} g (Bochner set integral)
- T = σ(e) > 0
- IntegrableOn g (Ioi e): split at e+1
  - Near e: g ≤ C·(t-e)^{-1/2}, use intervalIntegrable_rpow'
  - Near ∞: g ≤ (t-e)^{-3/2}, use integrableOn_Ioi_rpow_of_lt
- StrictAntiOn σ (Ici e)
- 0 < σ(x) < T for x ∈ (e,∞)
- ContinuousOn σ (Ici e)
- σ → 0 at Filter.atTop
- HasDerivAt σ (-g x) x for x > e (via FTC)
- Fact (0 < 2*T) instance

## S5: θ definition + injectivity

θ : ker(componentBitHom) → AddCircle(2T):
- θ(O) = 0
- θ(x, y<0) = mk(σ(x))        [lower branch: σ ∈ (0,T)]
- θ(x, y>0) = mk(-σ(x))       [upper branch: ≡ mk(2T-σ) ∈ (T,2T)]
- θ(e, 0) = mk(T)              [bottom 2-torsion]

Equivalently: θ(x,y) = if 0 ≤ y then mk(-σ x) else mk(σ x)
(Works at y=0 since σ(e)=T, -T≡T mod 2T.)

θ(-P) = -θ(P) definitional (negation flips y-sign).

Injectivity via Ico-representatives in [0, 2T):
- Use AddCircle.coe_eq_coe_iff_of_mem_Ico
- 4×4 case bash: cross cases killed by disjoint ranges,
  diagonal by StrictAntiOn.injOn for σ

## S6-S8: θ additivity (the crux)

Fix Q ∈ ker, Q ≠ O. Vary P = (x, +√f(x)) on upper branch, x ∈ (e,∞).

**Junction set F_Q ⊆ (e,∞), |F_Q| ≤ 3:**
- J1: P = -Q (sum → O). Lift jump = 2T. ✓ killed by AddCircle.
- J2: x₃ = e (sum → (e,0)). Lift jump = 2T. ✓ killed.
- J3: P = Q (doubling). NO jump — removable singularity.

**Per-piece constancy (S8 payoff):**
On each interval of (e,∞) \ F_Q:
- x₃(x) is smooth rational, y₃ has constant sign (IsPreconnected)
- S8 identity: dx₃/dx · (1/y₃) = 1/y₁
- ⇒ HasDerivAt (lift of defect) 0 x
- ⇒ constant by `constant_of_has_deriv_right_zero`

**Junction crossing (one-sided limits):**
- J1: σ(x₃) → 0 (x₃ → ∞), both limits = θ(Q)
- J2: σ(x₃) → T, mk(T) = mk(-T) by coe_period
- J3: chord → tangent, continuous (√f differentiable at x_Q)

**Bootstrap for degenerate cases:**
- Lower branch: apply to (-P, -Q), negate
- P = O: trivial
- P = (e,0): limit from x → e⁺
- Degenerate Q (2Q ∈ {O, (e,0)}): group-algebra via auxiliary generic R

## S9: Harvest

1. θ injective hom ⇒ E⁰[n] ↪ AddCircle(2T)[n]
2. |AddCircle(2T)[n]| = n (Mathlib: card_addOrderOf_eq_totient + sum_totient,
   or directly card_torsion_le_of_isSMulRegular)
3. Finiteness transfer: Set.Finite.of_finite_image
4. componentBitHom fiber argument: |E(ℝ)[n]| ≤ 2·|E⁰[n]| ≤ 2n

**Trap:** Nat.card of infinite sets = 0. Must establish finiteness BEFORE cardinality.

## Estimated LOC

| Step | LOC | Status |
|------|-----|--------|
| S0 | ~200 | In progress (subagent) |
| S4 | ~200 | Not started |
| S5 | ~100 | Not started |
| S6 | ~150 | Not started |
| S7-S8 | ~300 | Not started |
| S9 | ~100 | Not started |
| **Total** | **~1050** | |
