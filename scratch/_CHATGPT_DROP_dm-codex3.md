# Q2936: algebraic attack on Kubert C12 Tate table residual B

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`.
Namespace: `MazurProof.KubertBridgeN12`.

Current residual B is the axiom

```lean
axiom kubert_C12_table_of_tate_origin_order12 ... :
  KubertC12TateTableModel b c hb hDelta hOrder
```

This note gives a Lean-friendly replacement DAG. The key point is: avoid appealing to Kubert globally. Prove the Tate-normal-form multiples directly, reduce exact order 12 to one explicit polynomial `K12(b,c)=0`, then prove the rational parametrization of that polynomial by `q`.

## 0. Curve convention

For

```lean
def tateW (b c : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 }
```

the affine equation is

```text
y^2 + (1-c)*x*y - b*y = x^3 - b*x^2.
```

The inverse of an affine point `(x,y)` is

```text
-(x,y) = (x, -y - (1-c)*x + b).
```

## 1. Multiples of P=(0,0)

Let `P=(0,0)`. Direct chord/tangent calculation gives:

```text
-P  = (0,b)
2P  = (b, b*c)
3P  = (c, b-c)
4P  = ( b*(b-c)/c^2,
        b^2*(c^2+c-b)/c^3 )                         [c ≠ 0]
```

Derivation checks:

* tangent at `P` is `y=0`; third intersection is `(b,0)`, so `2P=(b,bc)`.
* line through `P` and `2P` is `y=c*x`; third intersection is `(c,c^2)`, so `3P=(c,b-c)`.
* line through `P` and `3P` has slope `(b-c)/c`; the third intersection and inversion give the displayed `4P`.

Lean statement shapes:

```lean
noncomputable def tateP2 (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some b (b*c) (by
    -- point membership; no nonsingularity issue for `Point.some` proof shape may differ locally
    dsimp [tateW]
    ring)

noncomputable def tateP3 (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some c (b-c) (by
    dsimp [tateW]
    ring)

noncomputable def tateP4 (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some
    (b*(b-c)/c^2)
    (b^2*(c^2+c-b)/c^3)
    (by
      dsimp [tateW]
      field_simp [hc]
      ring)
```

Actual group-law wrappers should be added after checking the local notation for point addition/scalar multiplication:

```lean
theorem tate_origin_twoP_eq
    (b c : ℚ) (hb : b ≠ 0) :
    2 • tateOriginAffine b c hb = tateP2 b c hb := by
  -- tangent y=0, third intersection (b,0), invert
  -- use the local Weierstrass affine group law API if convenient;
  -- otherwise prove through the existing addition formula lemma.
  sorry

theorem tate_origin_threeP_eq
    (b c : ℚ) (hb : b ≠ 0) :
    3 • tateOriginAffine b c hb = tateP3 b c hb := by
  -- line y=c*x through P and 2P
  sorry

theorem tate_origin_fourP_eq
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) :
    4 • tateOriginAffine b c hb = tateP4 b c hb hc := by
  -- line through P and 3P, slope `(b-c)/c`
  sorry
```

The first self-contained theorem to prove next is `tate_origin_threeP_eq`; it only needs the tangent computation for `2P` and one secant computation.

## 2. Polynomial condition for 12P=0

Use the long-Weierstrass division-polynomial invariants:

```text
a1 = 1-c, a2=-b, a3=-b, a4=0, a6=0
b2 = (1-c)^2 - 4*b
b4 = b*(c-1)
b6 = b^2
b8 = -b^3
```

For a point `R=(x,y)`,

```text
ψ2(R) = 2*y + a1*x + a3.
```

At `3P=(c,b-c)`:

```text
ψ2(3P) = b - c - c^2.
```

So `P` has order 6 exactly when

```text
b = c + c^2.
```

For exact order 12, `3P` has order 4, so `ψ4(3P)=0` and `ψ2(3P)≠0`. The non-`ψ2` factor of `ψ4` at `x=c` reduces to:

```lean
def tateC12_K (b c : ℚ) : ℚ :=
  c^6 + c^4 + b*c^4 - 5*b*c^3 + 10*b^2*c^2
    - b^3*c^2 - 9*b^3*c + 3*b^4
```

More explicitly, if

```text
Ψ4core(x) =
  2*x^6 + b2*x^5 + 5*b4*x^4 + 10*b6*x^3 + 10*b8*x^2
    + (b2*b8-b4*b6)*x + (b4*b8-b6^2),
```

then

```text
Ψ4core(c) = c * tateC12_K(b,c).
```

Lean identity snippet:

```lean
def tate_b2 (b c : ℚ) : ℚ := (1-c)^2 - 4*b
def tate_b4 (b c : ℚ) : ℚ := b*(c-1)
def tate_b6 (b c : ℚ) : ℚ := b^2
def tate_b8 (b c : ℚ) : ℚ := -b^3

def tatePsi4CoreAt3P (b c : ℚ) : ℚ :=
  2*c^6 + tate_b2 b c*c^5 + 5*tate_b4 b c*c^4 +
    10*tate_b6 b c*c^3 + 10*tate_b8 b c*c^2 +
    (tate_b2 b c*tate_b8 b c - tate_b4 b c*tate_b6 b c)*c +
    (tate_b4 b c*tate_b8 b c - tate_b6 b c^2)

-- If parser precedence complains about the final `tate_b6 b c^2`, write `(tate_b6 b c)^2`.

theorem tatePsi4CoreAt3P_eq_c_mul_K (b c : ℚ) :
    tatePsi4CoreAt3P b c = c * tateC12_K b c := by
  unfold tatePsi4CoreAt3P tateC12_K tate_b2 tate_b4 tate_b6 tate_b8
  ring
```

I recommend adding the corrected version with explicit parentheses:

```lean
def tatePsi4CoreAt3P (b c : ℚ) : ℚ :=
  2*c^6 + tate_b2 b c*c^5 + 5*tate_b4 b c*c^4 +
    10*tate_b6 b c*c^3 + 10*tate_b8 b c*c^2 +
    (tate_b2 b c*tate_b8 b c - tate_b4 b c*tate_b6 b c)*c +
    (tate_b4 b c*tate_b8 b c - (tate_b6 b c)^2)
```

Then the order-12 algebraic core should be stated as:

```lean
theorem tate_origin_order12_implies_K
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    c ≠ 0 ∧ b - c - c^2 ≠ 0 ∧ tateC12_K b c = 0 := by
  -- c=0 gives 4P=0.
  -- b-c-c^2=0 gives 6P=0.
  -- 12P=0 gives ψ4(3P)=0; since c≠0 and ψ2(3P)≠0, get K=0.
  sorry
```

Conversely:

```lean
theorem tate_origin_order12_of_K
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hc : c ≠ 0) (h6 : b - c - c^2 ≠ 0)
    (hK : tateC12_K b c = 0) :
    addOrderOf (tateOriginAffine b c hb) = 12 := by
  -- K=0 -> 4*(3P)=0 -> 12P=0.
  -- h6 -> 6P≠0.
  -- hc -> 4P≠0.
  -- hb -> 2P≠0.
  -- combine divisors of 12 to get exact order.
  sorry
```

This pair is a clean replacement for the group-law part of residual B.

## 3. Introduce the rational parameter `q`

The table parametrization is equivalent to the two equations

```text
b*(q+1) = c*(q^2+1)
c*(q+1)^3 = q*(q-1)*(3*q^2+1).
```

From these, with `q+1≠0`, one immediately gets the project’s definitions:

```lean
def tateC12_b (q : ℚ) : ℚ :=
  q * (q - 1) * (q ^ 2 + 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 4

def tateC12_c (q : ℚ) : ℚ :=
  q * (q - 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 3
```

Lean algebra snippets:

```lean
theorem tateC12_param_eqs_of_defs (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_b q * (q+1) = tateC12_c q * (q^2+1) ∧
    tateC12_c q * (q+1)^3 = q*(q-1)*(3*q^2+1) := by
  constructor
  · unfold tateC12_b tateC12_c
    field_simp [hq1]
    ring
  · unfold tateC12_c
    field_simp [hq1]
    ring

theorem tateC12_defs_of_param_eqs
    {b c q : ℚ} (hq1 : q + 1 ≠ 0)
    (hbc : b*(q+1) = c*(q^2+1))
    (hc : c*(q+1)^3 = q*(q-1)*(3*q^2+1)) :
    b = tateC12_b q ∧ c = tateC12_c q := by
  have hc' : c = tateC12_c q := by
    unfold tateC12_c
    field_simp [hq1]
    exact hc
  constructor
  · rw [hc'] at hbc
    unfold tateC12_b tateC12_c at hbc ⊢
    field_simp [hq1] at hbc ⊢
    nlinarith
  · exact hc'
```

The forward identity `K=0` under the definitions is a pure `field_simp; ring` theorem:

```lean
theorem tateC12_K_of_param (q : ℚ) (hq1 : q + 1 ≠ 0) :
    tateC12_K (tateC12_b q) (tateC12_c q) = 0 := by
  unfold tateC12_K tateC12_b tateC12_c
  field_simp [hq1]
  ring
```

Useful exactness denominator/nonzero facts:

```lean
theorem tateC12_c_ne_zero
    {q : ℚ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqm1 : q + 1 ≠ 0) :
    tateC12_c q ≠ 0 := by
  unfold tateC12_c
  have h3 : 3*q^2 + 1 ≠ 0 := by nlinarith [sq_nonneg q]
  field_simp [hq0, hq1, hqm1, h3]

theorem tateC12_not_order6
    {q : ℚ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) (hqm1 : q + 1 ≠ 0) :
    tateC12_b q - tateC12_c q - (tateC12_c q)^2 ≠ 0 := by
  unfold tateC12_b tateC12_c
  have h3 : 3*q^2 + 1 ≠ 0 := by nlinarith [sq_nonneg q]
  -- After simplification this is
  -- -2*q^3*(q-1)^3*(3*q^2+1)/(q+1)^6 ≠ 0.
  field_simp [hq0, hq1, hqm1, h3]
```

Depending on the local definition of `TateC12Good`, it should at least imply:

```lean
q ≠ 0, q ≠ 1, q + 1 ≠ 0
```

and any extra nonzero denominators such as `q^2+1` and `3*q^2+1` are automatic over `ℚ` by `nlinarith [sq_nonneg q]`.

## 4. Hard parametrization theorem replacing the table axiom

The remaining nontrivial algebra is the converse parametrization of the genus-0 curve `K12(b,c)=0`. Isolate it as a theorem independent of Weierstrass group law:

```lean
theorem tateC12_K_parametrization
    {b c : ℚ}
    (hb : b ≠ 0) (hc : c ≠ 0) (h6 : b - c - c^2 ≠ 0)
    (hK : tateC12_K b c = 0) :
    ∃ q : ℚ,
      TateC12Good q ∧ b = tateC12_b q ∧ c = tateC12_c q := by
  -- Pure plane-curve parametrization.
  -- Recommended proof route:
  -- 1. Use the known rational point at infinity / singular projection of `K12`.
  -- 2. Introduce q by the two equations:
  --      b*(q+1)=c*(q^2+1)
  --      c*(q+1)^3=q*(q-1)*(3*q^2+1)
  -- 3. Prove `q+1≠0`, then use `tateC12_defs_of_param_eqs`.
  sorry
```

This is the **first genuinely hard but self-contained theorem** to prove next. It is independent of elliptic-curve group APIs and should live before the residual axiom. Once it is available, residual B becomes a short assembly:

```lean
theorem kubert_C12_table_of_tate_origin_order12_proof
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    KubertC12TateTableModel b c hb hDelta hOrder := by
  obtain ⟨hc, h6, hK⟩ :=
    tate_origin_order12_implies_K b c hb hDelta hOrder
  obtain ⟨q, hgood, hbq, hcq⟩ :=
    tateC12_K_parametrization hb hc h6 hK
  exact ⟨q, hgood, hbq, hcq⟩
```

## 5. Suggested theorem order to add before the axiom

1. **Coordinate formulas:**
   ```lean
   tate_origin_twoP_eq
   tate_origin_threeP_eq
   tate_origin_fourP_eq
   ```
   These are direct line/tangent computations.

2. **Division-polynomial core:**
   ```lean
   tatePsi4CoreAt3P_eq_c_mul_K
   tate_origin_order12_implies_K
   tate_origin_order12_of_K
   ```

3. **Pure Kubert parametrization:**
   ```lean
   tateC12_param_eqs_of_defs
   tateC12_defs_of_param_eqs
   tateC12_K_of_param
   tateC12_K_parametrization
   ```

The safest next single theorem is:

```lean
theorem tatePsi4CoreAt3P_eq_c_mul_K (b c : ℚ) :
    tatePsi4CoreAt3P b c = c * tateC12_K b c := by
  unfold tatePsi4CoreAt3P tateC12_K tate_b2 tate_b4 tate_b6 tate_b8
  ring
```

It is small, self-contained, and fixes the exact polynomial that the rest of residual B should target.
