# Q1385 (dm1/dm3): Kubert bridge for noncyclic `N=12,14,16`

## Executive answer

For Mazur-torsion formalization:

* **`N=12`: yes**, it can use essentially the same bridge pattern as `N=10`: cyclic `C12` Kubert/Tate family plus the full-2-torsion discriminant-square condition.
* **`N=14`: no, not in the same way over `ℚ`**.  A noncyclic `C2 × C14` subgroup already implies a rational point of order `14`, so it is better to discharge it by the cyclic `C14` exclusion, i.e. the rational-points computation on `X_1(14)`.  The convenient parametrizations are over quadratic fields, not a rational one-parameter Kubert family over `ℚ`.
* **`N=16`: no, not in the same way over `ℚ`**.  A noncyclic `C2 × C16` subgroup already implies a rational point of order `16`; use the cyclic `C16` exclusion.  The known normal forms for `16` naturally involve quadratic-field/nested-square conditions, not a genus-zero `t : ℚ` Kubert family.

So the Lean structure should be:

```lean
-- C10 and C12: cyclic genus-zero family + full-2 square obstruction.
axiom kubert_C10_full2_square_obstruction : ...
axiom kubert_C12_full2_square_obstruction : ...

-- C14 and C16: reduce noncyclic immediately to cyclic exclusions.
theorem no_C2xC14_of_no_C14 : noCyclic14 → noNoncyclic2x14 := ...
theorem no_C2xC16_of_no_C16 : noCyclic16 → noNoncyclic2x16 := ...
```

## General full-2 condition

For a curve in the form

```text
E : y^2 = x^3 + A x^2 + B x = x (x^2 + A x + B),
```

the point `(0,0)` is a rational point of order `2`.  The curve has full rational 2-torsion iff the quadratic factor

```text
x^2 + A x + B
```

splits over `ℚ`, equivalently

```text
A^2 - 4B is a square in ℚ.
```

This is the same square-discriminant bridge used in the `N=10` case.

## `N=12`: the usable C10-style bridge

A convenient `C12` family in the form `y^2 = x^3 + A12(t) x^2 + B12(t) x` is:

```text
A12(t) = 2 * (3*t^8 + 24*t^6 + 6*t^4 - 1)
B12(t) = (t^2 - 1)^6 * (1 + 3*t^2)^2
```

with the usual exclusions to avoid singular/cuspidal parameters, in particular `t ≠ ±1`.  This is the `Γ_t`/`Γ_{a,b}` model in the geometric paper; it is equivalent to Kubert's Tate normal form for `C12`.

Kubert's Tate normal form is

```text
E(b,c): y^2 + (1-c)xy - b y = x^3 - b x^2,
```

with

```text
τ = r/s,
m = (3τ - 3τ^2 - 1)/(τ - 1),
f = m/(1 - τ),
d = m + τ,
c = f*(d - 1),
b = c*d.
```

After transforming to the `y^2 = x^3 + A x^2 + B x` model and reparametrizing, the above `A12,B12` result.

The full-2 discriminant is especially clean.  Let `x = t^2` and

```text
F = 3*t^8 + 24*t^6 + 6*t^4 - 1.
```

Then

```text
A12(t)^2 - 4*B12(t)
  = 256 * t^6 * (t^2 + 1)^3 * (3*t^2 - 1).
```

Since `256*t^6*(t^2+1)^2` is already a square, the full-2 condition reduces to the obstruction curve

```text
Y^2 = (t^2 + 1) * (3*t^2 - 1)
     = 3*t^4 + 2*t^2 - 1.
```

Thus the exact Lean bridge axiom/lemma should be:

```lean
/-- Kubert C12 plus full 2-torsion gives the C12 obstruction curve. -/
axiom kubert_C12_square :
  ∀ {E : Type} [/* elliptic curve over ℚ */],
    HasSubgroup_C2xC12 E →
      ∃ t y : ℚ,
        t ≠ 1 ∧ t ≠ -1 ∧
        y^2 = 3*t^4 + 2*t^2 - 1
```

Then the arithmetic obstruction should be a separate theorem:

```lean
/-- The only rational points on the C12 obstruction are cuspidal/singular. -/
axiom C12_obstruction_no_noncuspidal_Qpoints :
  ∀ t y : ℚ,
    y^2 = 3*t^4 + 2*t^2 - 1 →
    t = 1 ∨ t = -1
```

I would formalize `C12_obstruction_no_noncuspidal_Qpoints` as a standalone genus-one/rank-zero computation, not inside the Kubert bridge.

## `N=14`: do not use the C10/C12 bridge over `ℚ`

There is no genus-zero rational Kubert parameter `t : ℚ` for rational `C14` torsion.  A rational `C14` point would be a rational point on `X_1(14)`, and the relevant obstruction is already the cyclic `C14` exclusion.

A useful quadratic-field condition from the geometric/Rabarison-style parametrization is:

```text
z^2 = D14(u) = 1 - 2u + u^2 + 4u^3.
```

Over a field containing `z = sqrt(D14(u))`, one may set

```text
v = u * (1 - 4u - u^2 + 2z)/(u - 1)^2
```

and obtain a model in the `y^2 = x^3 + A x^2 + B x` shape with

```text
A14(u,z) = 3*u^2 + 2*u^3*v + v^2 - 2
B14(u,z) = (u^2 - 1)^3 * (v^2 - 1).
```

This is useful for quadratic fields, but for Mazur over `ℚ`, if `z ∈ ℚ` and the parameter is noncuspidal, then one already has cyclic `C14` over `ℚ`, impossible.  Therefore the noncyclic exclusion should simply be:

```lean
/-- Noncyclic `C2 × C14` implies cyclic `C14`; use the cyclic modular-curve exclusion. -/
theorem no_C2xC14_of_no_C14
    (h14 : ∀ E, ¬ HasPointOfOrder E 14) :
    ∀ E, ¬ HasSubgroup_C2xC14 E := by
  intro E h
  exact h14 E h.hasPointOfOrder14
```

The exact names will depend on your torsion API, but this is the right proof shape.

## `N=16`: same conclusion, even more strongly

For `N=16`, the situation is even less like `N=10`.  The normal forms in the literature naturally live over quadratic fields.  One convenient quadratic-field consequence is: for `m ∈ ℚ \ {−1,0,1}`, define

```text
d1(m) = (m^4 - 1) * (m^2 - 2m - 1)
d2(m) = m * (m^2 + 1) * (m^2 + 2m - 1).
```

Then over each `ℚ(sqrt(d_i(m)))` there are curves with torsion `C16`.  One model over `ℚ(sqrt(d1))` is

```text
A16_1(m) = (m^4 - 1)^2 - 4*m^2*(m^4 + 1)
B16_1(m) = 16*m^8
```

so

```text
y^2 = x^3 + A16_1(m) x^2 + B16_1(m) x.
```

Another normal form over `ℚ(sqrt(d2))` is the Tate-like equation

```text
y^2 + (1-c)xy - b y = x^3 - b x^2
```

with

```text
b = - m*(m - 1)^2/(m^2 + 1)^2
c = - 2*m*(m - 1)^2/((m^2 + 1)*(m + 1)^2).
```

Again, this is not a rational Kubert family for `C16` over `ℚ`.  If a rational elliptic curve had a subgroup `C2 × C16`, it would already have a rational point of order `16`; use the cyclic `C16` exclusion:

```lean
/-- Noncyclic `C2 × C16` implies cyclic `C16`; use the cyclic modular-curve exclusion. -/
theorem no_C2xC16_of_no_C16
    (h16 : ∀ E, ¬ HasPointOfOrder E 16) :
    ∀ E, ¬ HasSubgroup_C2xC16 E := by
  intro E h
  exact h16 E h.hasPointOfOrder16
```

## What to formalize

Recommended Lean declarations:

```lean
-- Shared full-2 condition for `y^2=x^3+A*x^2+B*x`.
def full2Disc (A B : ℚ) : ℚ := A^2 - 4*B

-- C12 coefficients.
def A12 (t : ℚ) : ℚ := 2 * (3*t^8 + 24*t^6 + 6*t^4 - 1)
def B12 (t : ℚ) : ℚ := (t^2 - 1)^6 * (1 + 3*t^2)^2

theorem C12_disc_factor (t : ℚ) :
    full2Disc (A12 t) (B12 t)
      = 256 * t^6 * (t^2 + 1)^3 * (3*t^2 - 1) := by
  ring

-- Bridge from C2×C12 to obstruction curve.
axiom kubert_C12_full2_obstruction :
  ∀ E, HasSubgroup_C2xC12 E →
    ∃ t y : ℚ, t ≠ 1 ∧ t ≠ -1 ∧ y^2 = 3*t^4 + 2*t^2 - 1

-- Separate arithmetic/rank-zero computation.
axiom C12_obstruction_no_noncuspidal_Qpoints :
  ∀ t y : ℚ, y^2 = 3*t^4 + 2*t^2 - 1 → t = 1 ∨ t = -1

-- C14/C16 should reduce to cyclic exclusions, not to new Kubert full-2 bridges.
```

## Source notes

* The genus-zero `C12` family and its equivalence to Kubert's Tate normal form are given in the cited geometric paper, Theorem 5 and the following Kubert comparison.
* The `C14` quadratic-field condition is `z^2 = 1 - 2u + u^2 + 4u^3`; the same paper gives the model coefficients via `v` and the transformation to `y^2=x^3+A x^2+B x`.
* The `C16` quadratic-field normal forms are given there in Corollary 10 and formulas (3), (4), (5).

Bottom line: implement `N=12` by the C10-style bridge.  Implement `N=14` and `N=16` by reducing the noncyclic cases to the already-needed cyclic exclusions.
