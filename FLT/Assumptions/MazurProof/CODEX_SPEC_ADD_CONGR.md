# Codex Spec: close `add_congr` sorry in N18AddCongr.lean

## Target
Close the sorry at `N18AddCongr.lean:294` in theorem `add_congr`.

## Statement
```lean
theorem add_congr (P Q : E0Point)
    (hP : 1 ≤ v (zParam P)) (hQ : 1 ≤ v (zParam Q)) :
    v (zParam P) + v (zParam Q) ≤ v (zParam (P + Q) - zParam P - zParam Q)
```

The O-cases (P=O or Q=O) are already dispatched. The remaining sorry is for
both P = (x₁,y₁) and Q = (x₂,y₂) finite, with `1 ≤ ordPi(-x₁/y₁)` and
`1 ≤ ordPi(-x₂/y₂)`.

## Curve
E0 = [a₁,a₂,a₃,a₄,a₆] = [1,-1,1,-5,5] (Cremona 162.c3 base-changed to L).

## Proof architecture (from Q4613 design, verified)

### Chart coordinates
t = -x/y = zParam(P), w = -1/y. On E0: v(t) = r ≥ 1, v(w) = 3r.

Chart equation: G(t,w) = w - tw + t²w - w² + 5tw² - 5w³ - t³ = 0.

### Key polynomial definitions (for E0 specifically)
```
A(m) = 1 - m - 5m² + 5m³         -- coeff of -t³ in G(t,mt+b)
B(m,b) = m - b + m² - 10mb + 15m²b
C(m,b) = m - b - 2mb + 5b² - 15mb²
D(b) = b - b² - 5b³ = b(1 - b - 5b²)
H(m,b) = -8m + 16m² - 4b + 20mb
```

### Identity (8) — the decisive cross-term identity
```
A·d·(t₃ - t₁ - t₂) = b·H - A·t₁t₂·(1+m) - A·b·u
```
where u is the third Vieta root and d = 1-(1+m)u-b.
This follows from the coefficient identity `B(1-b) - (1+m)C = b·H` (ring)
plus the first two Vieta equations.

### Three branches of Point.add
1. **Inverse (P+Q=O):** t⁻ = -t/(1-t-w), d⁻ = 1-t-w is a unit.
   Error = t + t⁻ = -t(t+w)/d⁻. v(t+w) = r (since v(w)=3r > v(t)=r).
   v(error) = 2r ≥ r+r. ✓

2. **Distinct-x:** Secant slope m = (w₁-w₂)/(t₁-t₂) via the factorization
   (w₁-w₂)·SU = (t₁-t₂)·SN where SU = 1 + O(v≥1) is a unit.
   v(m) ≥ 2r where r = min(r₁,r₂). Then v(b) ≥ 3r (from b = w₁ - m·t₁).
   Product Vieta: A·t₁t₂·u = D(b) = b·(1-b-5b²), the factor is a unit,
   so v(b) = v(t₁) + v(t₂) + v(u) and v(u) ≥ r.
   Feed identity (8): all terms on RHS have v ≥ r₁+r₂,
   A and d are units, so v(t₃ - t₁ - t₂) ≥ r₁+r₂. ✓

3. **Doubling:** Tangent slope from G_t + m·G_w = 0 at the double point.
   v(m) ≥ 2r, v(b) = v(w) = 3r. Product Vieta gives v(u) = r.
   Identity (8) gives v(t₃ - 2t) ≥ 2r. ✓

### Important note on junk values
If `zParam(P+Q) - zParam P - zParam Q = 0`, then `ordPi 0 = 0` which makes
the inequality `r₁+r₂ ≤ 0` false. BUT: per Fable's analysis, in the inverse
branch the error is `-t(t+w)/d⁻ ≠ 0` (since t ≠ 0, d⁻ is a unit, and t+w ≠ 0
because v(t) = r ≠ 3r = v(w)). In the other branches, the error can only be
zero if the Vieta structure degenerates, which the unit arguments prevent.

If the zero case is genuinely problematic, restate the theorem with a disjunction:
```
zParam (P + Q) - zParam P - zParam Q = 0 ∨
v (zParam P) + v (zParam Q) ≤ v (zParam (P + Q) - zParam P - zParam Q)
```

### Available toolbox (all in N18AddCongr.lean, sorry-free)
- `ordPi_mul`, `ordPi_div`, `ordPi_neg`, `ordPi_zero`, `ordPi_one`
- `ordPi_add_ge` (ultrametric), `ordPi_add_eq_of_lt` (strict domination)
- `zero_le_ordPi_intCast` (integer coefficients have v ≥ 0)
- `val_coords` (STEP 1: v(x) = -2r, v(y) = -3r for finite kernel points)

### Mathlib API for Point.add
- `WeierstrassCurve.Affine.Point.add_of_Y_eq` (inverse branch)
- `WeierstrassCurve.Affine.addX`, `addY`, `negY` (explicit formulas)
- `WeierstrassCurve.Affine.slope_of_X_ne`, `slope_of_Y_ne`

## Deliverable
Write the proof in a NEW file `N18AddCongrProof.lean` that exports a theorem
with the same signature. Do NOT modify `N18AddCongr.lean` directly.

## Verification
`lake env lean FLT/Assumptions/MazurProof/N18AddCongrProof.lean` must compile
with no sorry. `#print axioms` must show only {propext, Classical.choice, Quot.sound}.
