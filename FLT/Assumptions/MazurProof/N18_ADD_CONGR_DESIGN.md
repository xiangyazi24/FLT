# N18 Package I `add_congr` — full pointwise design (ChatGPT Q4613, verified sound)

`add_congr` is the REAL live analytic core of the E₀ route (the multi-round audit confirmed
Package II is off the critical path; the live filtration uses `val_three_smul_ge` ⟸ `add_congr`).
Target: for `E0 : y²+xy+y = x³-x²-5x+5`, `z=-x/y`, `v=ordPi`:
`1 ≤ v(zP), 1 ≤ v(zQ) ⟹ v(zP)+v(zQ) ≤ v(z(P+Q) - zP - zQ)`.

## BUG in the naive approach (Q4613 caught it; I verified)
The proposed STEP-2 affine-slope bound `v(ℓ) ≥ -min(v zP, v zQ)` is **FALSE** in the distinct-x
branch. With `r_P<r_Q`: `v(y_Q-y_P)=-3r_Q`, `v(x_Q-x_P)=-2r_Q` (unequal-valuation ultrametric),
so `v(ℓ)=-r_Q = -max(r_P,r_Q)`, strictly below `-min`. (Depths 1,2 → `v(ℓ)=-2`, not `≥-1`.)
Replacing min by max does not help either: as Q→-P the affine line → vertical, `v(ℓ)≈-v(u)`
unbounded; the pole of ℓ is cancelled by its intercept, and bounding ℓ alone discards that
cancellation. **The fix: work with the normalized chart line, whose intercept `b` carries both
inputs — never the affine slope.**

## Correct architecture
`Mathlib Point.add branch → (t,w)-normalized line → Vieta → identity (8) → ultrametric bound.`
Identity chart: `t=-x/y=z(P)`, `w=-1/y`; `v(t)=r`, `v(w)=3r`.
Exact chart equation (from the Weierstrass relation, `field_simp`+`ring`):
```
G(t,w) := w - t³ - t·w + t²·w - w² + 5t·w² - 5w³ = 0.
```
Line `w=mt+b` substituted into G:  `G(t,mt+b) = -A(m)T³ - B(m,b)T² + C(m,b)T + D(b)` with
```
A(m)=1-m-5m²+5m³         (unit when v(m)>0)
B(m,b)=m-b+m²-10mb+15m²b
C(m,b)=m-b-2mb+5b²-15mb²
D(b)=b-b²-5b³
```
Vieta (roots t₁,t₂,u): `A(t₁+t₂+u)+B=0`, `A(t₁t₂+(t₁+t₂)u)+C=0`, `A·t₁t₂u = D = b(1-b-5b²)`.

**Decisive cross-term identity (8):**
```
A·d·(t₃ - t₁ - t₂) = b·H - A(t₁t₂)(1+m) - A·b·u,   H(m,b) := -8m+16m² -4b+20mb,
```
where third-point param `t₃ = -u/d`, `d = 1-(1+m)u-b` (a unit). Uses only the coefficient
identity `B(1-b)-(1+m)C = b·H` (one `ring`) + the first two Vieta eqns.

## Valuation bounds (the exact replacement for the false slope bound)
Secant (distinct-x), `r=min(r₁,r₂)`:  from `secantUnit·m = secantNum` with `v(secantUnit)=0`,
`v(secantNum)≥2r`:  **`v(m)≥2r`**, then `v(b)≥3r`; unit `1-b-5b²`; Vieta sum `v(u)≥r`; and the
**product Vieta** `A·t₁t₂u=b(unit)` gives the strong **`v(b)=r₁+r₂+v(u) ≥ r₁+r₂+r`**. Feeding
(8): `v(bH)≥r₁+r₂+r`, `v(A t₁t₂(1+m))=r₁+r₂`, `v(Abu)≥r₁+r₂+2r`, `A,d` units ⟹
`r₁+r₂ ≤ v(t₃-t₁-t₂)`. ✓
Doubling (t₁=t₂=t): tangent `m = (3t²+w-2tw-5w²)/(1-t+t²-2w+10tw-15w²)`, denom a unit; `v(m)≥2r`;
exact `U·b = w(t+w-2)` with `v(t+w-2)=0` ⟹ `v(b)=v(w)=3r`; product Vieta `v(u)=r`; (8) with
`t₁t₂=t²` ⟹ `2r ≤ v(t₃-2t)`. ✓
Vertical/inverse (`Point.add_of_Y_eq` → 0): `-P` has `t⁻=-t/(1-t-w)`, `d⁻=1-t-w` unit,
`t+t⁻ = -t(t+w)/d⁻`, `v(t+w)≥r` ⟹ `2r ≤ v(0-t-t⁻)`. ✓

## Lean skeleton (key lemmas — Q4613 gave compile-shaped bodies)
- `chartG_eq_zero (hE)(hy) : chartG (-x/y) (-1/y) = 0`  — `field_simp; linear_combination -hE`.
- `E0Chart.{G,A,B,C,D,poly,H}` + `G_line : G t (m*t+b) = poly m b t` (`simp;ring`), `BC_factor` (`ring`).
- `secant_vieta` / `tangent_vieta` : produce the three Vieta eqns (`field_simp;ring` / `linear_combination`).
- `tangent_double_root` : `-3A t² -2B t + C = 0` via `G_t + m G_w = 0` (`field_simp;ring`).
- `secant_m_identity` : `secantUnit·((w₁-w₂)/(t₁-t₂)) = secantNum` (`field_simp; linear_combination h₁-h₂`).
- `error_factor_cleared` : the denominator-cleared identity (8) (`rw;linear_combination (b-1)hsum+(1+m)hpair`).
- `z_add_eq_chart` : bridges Mathlib `addX/negAddY/addY/slope` to `t₃=-u/d`. `x_u=u/(mu+b)=ℓ²+ℓ+1-x₁-x₂`
  via `affine_x_sum_coeff` (`ring`), `ℓ=m/b`.
- Main `add_congr` : `rcases` the two O-cases; `by_cases hvert`/`hx` → the three `Point.add`
  rewrite lemmas `add_of_Y_eq`, `add_self_of_Y_ne`, `add_of_X_ne`; each branch → its `*_chart_error_ord_ge`.
- Valuation helpers needed: `ordPi_{zero,one,neg,mul,pow,div,add_ge,add_eq_min_of_ne,ofNat_nonneg}`
  + `ordPi_add_ge_of_ge`, `ordPi_sub_ge_of_ge`, `ordPi_one_sub_eq_zero`. Keep finite levels as `ℤ`
  (`ordPi t = r`), rewrite before `omega` (don't `omega` on raw `WithTop ℤ`).

## Model caveat (from Q4615, cross-check)
The [3]-series on the RATIONAL model (1,-1,1,-5,5) has cubic coeff valuation 6, not 1; the
supersingular order-3 point's `v(z)=1` holds on the GOOD integral model (`zGood ≠ zParam`).
`add_congr` itself is a LOWER-bound statement and holds on the rational model (used above), but
constructing the full `FormalKernelData` (`val_three_smul_ge` tightness, `red`, `vpi`) may need the
good-model transport. Flag for the FormalKernelData step, not for `add_congr`.

_Source: ChatGPT Q4613 (delivery failed to Notion/GitHub — captured here verbatim-in-substance).
Bug claim independently verified. This is the blueprint for the live crux._
