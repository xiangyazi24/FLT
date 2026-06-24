## Verdict

The **isogeny proof is not currently available as a short Mathlib route**. I would not plan around a declaration like “multiplication-by-`n` as an isogeny of degree `n²`” plus “separable isogeny kernel has cardinality = degree”; I did not find that API in the current `WeierstrassCurve` elliptic-curve namespace.

The **division-polynomial degree theory is real and useful**, but it is not enough by itself. Mathlib has the polynomials and their expected degrees, but the missing bridge is still substantial: a theorem saying that the roots of the division polynomials are exactly the `x`-coordinates of affine `n`-torsion points, together with separability of those division polynomials when `(n : k) ≠ 0`.

So the shortest realistic route is:

```lean
division-polynomial correctness + separability
→ root count by Polynomial.card_rootSet_eq_natDegree
→ 2-points-over-each-non-2 x-coordinate
→ Nat.card E[n] = n^2
```

The single hardest missing Mathlib lemma is the **division-polynomial kernel characterization for scalar multiplication**.

---

## 1. Multiplication-by-`n` / isogeny route

As far as the current Mathlib docs show, there is no ready-to-use API of the form

```lean
WeierstrassCurve.mulBy n : E ⟶ E
degree_mulBy : degree (mulBy n) = n^2
separable_mulBy_of_natCast_ne_zero : ...
card_kernel_eq_degree_of_separable_isogeny : ...
```

or analogous `WeierstrassCurve.Isogeny` declarations. The elliptic-curve files do have point addition, doubling, projective formulas, and division polynomials, but not an isogeny layer with degrees and kernel-cardinality theorems.

If such an API existed, your theorem would indeed be the cleanest proof:

```lean
E[n] = ker [n]
#[ker [n]] = deg [n] = n^2
```

under separability of `[n]`, i.e. `(n : k) ≠ 0`. But that stack appears absent, so this is not the shortest current Mathlib-grounded route.

---

## 2. Division-polynomial API: what exists

The relevant imports are:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Module.Torsion.Basic
```

Mathlib defines the following division-polynomial objects:

```lean
WeierstrassCurve.ψ₂
WeierstrassCurve.Ψ₂Sq
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ
```

The file explicitly says `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, and `φ` are the main definitions, and also explicitly says that the bivariate `ωₙ` polynomials are still TODO. That matters because the full coordinate formula for `[n]P` needs the `y`-coordinate polynomial as well as the `x`-coordinate formula. citeturn964713view0

The key relation for 2-torsion is already there:

```lean
WeierstrassCurve.Ψ₂Sq_eq
```

with

```lean
W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly
```

so `Ψ₂Sq` is the cubic

```lean
4*X^3 + b₂*X^2 + 2*b₄*X + b₆
```

as expected. citeturn964713view0

The degree file gives the expected leading degrees. In prose, it states:

```text
preΨₙ has degree (n² - 4)/2 if n is even,
preΨₙ has degree (n² - 1)/2 if n is odd,
ΨSqₙ has degree n² - 1,
Φₙ has degree n².
```

under the expected nonzero-characteristic hypotheses. citeturn302599view0

The concrete declarations you want are:

```lean
WeierstrassCurve.natDegree_preΨ'
```

with shape

```lean
(W.preΨ' n).natDegree
  = (n^2 - if Even n then 4 else 1) / 2
```

assuming

```lean
h : (n : k) ≠ 0
```

and also

```lean
WeierstrassCurve.preΨ'_ne_zero
WeierstrassCurve.leadingCoeff_preΨ'
WeierstrassCurve.coeff_preΨ'_ne_zero
```

for the same polynomial. citeturn125516view1

For the integer-indexed version, use:

```lean
WeierstrassCurve.natDegree_preΨ
```

with shape

```lean
(W.preΨ n).natDegree
  = (n.natAbs^2 - if Even n then 4 else 1) / 2
```

again assuming the cast of `n` is nonzero. citeturn125516view1

For the squared denominator polynomial:

```lean
WeierstrassCurve.natDegree_ΨSq
```

has shape

```lean
(W.ΨSq n).natDegree = n.natAbs^2 - 1
```

under `[NoZeroDivisors k]` and `(n : k) ≠ 0`. citeturn125516view0

For the `x`-numerator polynomial:

```lean
WeierstrassCurve.natDegree_Φ
```

has shape

```lean
(W.Φ n).natDegree = n.natAbs^2
```

with only `[Nontrivial k]`. citeturn302599view3

Important: **do not count distinct `x`-coordinates using `ΨSq` and its degree**. `ΨSq` is squared in the odd case and partly squared in the even case. It has degree `n² - 1`, but its distinct roots are not `n² - 1`. For counting torsion, use `preΨ' n` for the non-2-torsion `x`-coordinates, and handle 2-torsion separately.

---

## 3. What Mathlib does not appear to have yet

I did not find a theorem of the form:

```lean
P ∈ E[n] ↔ eval divisionPolynomial n P.x = 0
```

or

```lean
n • P = 0 ↔ (W.preΨ' n).eval x = 0
```

for affine points. The division-polynomial docs say evaluation recovers the classical definitions up to the Weierstrass equation, but they do not expose the needed scalar-multiplication correctness theorem; and `ωₙ`, needed for a full `[n]P = (...)` coordinate formula, is explicitly TODO. citeturn964713view0

The theorem you really need to add is something like this, not necessarily with exactly this statement:

```lean
lemma preΨ'_root_iff_exists_non2_n_torsion_x
    [Field k] [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) {x : k} :
    (W.preΨ' n).eval x = 0 ↔
      ∃ y hxy,
        let P : (W⁄k).Point := .some x y hxy
        n • P = 0 ∧ 2 • P ≠ 0
```

For even `n`, the non-2 condition is essential: the 2-torsion `x`-coordinates are roots of `Ψ₂Sq`, not of `preΨ' n`. For odd `n`, the condition `2 • P ≠ 0` is automatic for nonzero `n`-torsion because `Nat.Coprime n 2`.

You also need separability:

```lean
lemma preΨ'_separable_of_natCast_ne_zero
    [Field k] [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable
```

and, for the even case,

```lean
lemma Ψ₂Sq_separable_of_two_ne_zero
    [Field k] [W.IsElliptic]
    (h2 : (2 : k) ≠ 0) :
    W.Ψ₂Sq.Separable
```

Those are not just nuisance lemmas. They are the hard algebraic geometry hidden behind “`[n]` is étale when char ∤ n.”

---

## 4. Exact counting once the missing bridge exists

For root counting, Mathlib gives the right general polynomial tools. `Polynomial.rootSet p K` is the set of distinct roots, and `Polynomial.card_rootSet_eq_natDegree` says that if `p` is separable and splits, then the number of distinct roots equals `p.natDegree`. citeturn547119view0turn302599view6

A separably closed field gives splitting of separable polynomials through:

```lean
IsSepClosed.splits_domain
IsSepClosed.splits_codomain
```

The `IsSepClosed` docs state that `IsSepClosed k` means every separable polynomial over `k` splits, and expose those splitting lemmas. citeturn151994view0

So after proving `preΨ'_separable_of_natCast_ne_zero`, the root count is basically:

```lean
have hsep : (W.preΨ' n).Separable :=
  preΨ'_separable_of_natCast_ne_zero (W := W) hn

have hsplit :
    (Polynomial.map (algebraMap k k) (W.preΨ' n)).Splits :=
  IsSepClosed.splits_domain (W.preΨ' n) hsep

have hrootcard :
    Fintype.card ((W.preΨ' n).rootSet k)
      = (W.preΨ' n).natDegree :=
  Polynomial.card_rootSet_eq_natDegree hsep hsplit

rw [W.natDegree_preΨ' hn] at hrootcard
```

up to `simp` around `Polynomial.map_id`.

Now split by parity.

### Odd `n`

For odd `n`, all nonzero `n`-torsion points are non-2-torsion. The affine nonzero `n`-torsion points come in pairs

```lean
P, -P
```

with the same `x`-coordinate and distinct `y`-coordinates. Thus each root of `preΨ' n` gives exactly two affine torsion points, and then you add the point at infinity:

\[
\#E[n] = 1 + 2 \cdot \frac{n^2 - 1}{2} = n^2.
\]

Lean target helper:

```lean
lemma card_nTorsion_odd
    [IsSepClosed k] [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) (hnodd : Odd n) :
    Nat.card (W.nTorsion n) = n^2 := by
  -- root count of W.preΨ' n
  -- every root gives exactly two affine points
  -- add ∞
```

The “exactly two affine points over the same `x`” part should be a local affine lemma: if one point is `Point.some x y h`, the other is its negation with `y = -y - a₁*x - a₃`; they are equal iff the point is 2-torsion.

### Even `n`

For even `n`, the 2-torsion subgroup is contained in `E[n]`. Since `(n : k) ≠ 0`, evenness implies `(2 : k) ≠ 0`.

You count:

\[
\#E[2] = 4
\]

and then the non-2 `n`-torsion points via `preΨ' n`:

\[
\deg(preΨ'_n)=\frac{n^2-4}{2}.
\]

Each such root gives two points, so

\[
\#E[n] = 4 + 2 \cdot \frac{n^2-4}{2} = n^2.
\]

Lean target helper:

```lean
lemma card_nTorsion_even
    [IsSepClosed k] [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) (hneven : Even n) :
    Nat.card (W.nTorsion n) = n^2 := by
  -- prove card E[2] = 4 using W.Ψ₂Sq_eq
  -- count non-2 torsion by roots of W.preΨ' n
  -- combine disjoint union
```

The 2-torsion count should be a standalone lemma:

```lean
lemma card_twoTorsion
    [IsSepClosed k] [W.IsElliptic]
    (h2 : (2 : k) ≠ 0) :
    Nat.card (W.nTorsion 2) = 4
```

Its proof uses:

```lean
W.Ψ₂Sq_eq
```

to identify the 2-torsion cubic, plus separability/splitting/root-counting. `Ψ₂Sq` is explicitly equal to `twoTorsionPolynomial.toPoly`. citeturn964713view0

---

## 5. Torsion submodule API

For your definition

```lean
E.nTorsion n = Submodule.torsionBy ℤ (E⁄k).Point n
```

the important simplifier is:

```lean
Submodule.mem_torsionBy_iff
```

which rewrites membership as scalar annihilation:

```lean
x ∈ Submodule.torsionBy R M a ↔ a • x = 0
```

Mathlib defines `Submodule.torsionBy R M a` as the kernel of scalar multiplication by `a`, and the docs state exactly that it contains the elements satisfying `a • x = 0`. citeturn547119view2turn547119view3

So most local goals should start with:

```lean
simp [E.nTorsion, Submodule.mem_torsionBy_iff]
```

and then normalize the scalar action:

```lean
change (n : ℤ) • P = 0
-- or convert to `n • P = 0` using zsmul/nsmul simp lemmas
```

---

## 6. Finiteness

For the restricted theorem

```lean
theorem n_torsion_finite_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Finite (E.nTorsion n)
```

the division-polynomial route is easier than the exact cardinal theorem. You only need the **one-sided** correctness lemma:

```lean
n • P = 0 → P = 0 ∨
  (W.preΨ' n).eval x = 0 ∨ W.Ψ₂Sq.eval x = 0
```

depending on parity. Then the possible `x`-coordinates lie in the roots of a nonzero polynomial, and for each `x` the Weierstrass equation has at most two `y`-values. Mathlib has `Polynomial.finite_setOf_isRoot` for the finiteness of roots of a nonzero polynomial, and `Polynomial.card_roots'` / `Polynomial.card_roots` for root-count bounds. citeturn810022view0

For your stronger statement

```lean
theorem n_torsion_finite {n : ℕ} (hn : 0 < n) :
  Finite (E.nTorsion n)
```

with **no** assumption `(n : k) ≠ 0`, the current division-polynomial degree file is not enough. When `char k ∣ n`, the leading-coefficient hypotheses used by `natDegree_preΨ'` and `natDegree_ΨSq` fail, and the separable-root-count argument is the wrong tool. The theorem is mathematically true, but a short Mathlib proof would need either the absent finite-isogeny/multiplication-map theory or a separate inseparable/Frobenius analysis.

So I would prove first:

```lean
theorem n_torsion_finite_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Finite (E.nTorsion n)
```

and let

```lean
n_torsion_card
```

produce finiteness automatically under the same hypothesis.

---

## 7. Realistic shortest implementation stack

Add these lemmas in this order.

```lean
lemma affine_same_x_eq_or_eq_neg
    {P Q : (W⁄k).Point}
    (hx : xCoord P = xCoord Q) :
    P = Q ∨ P = -Q
```

You may already have this through `xRep`/projective point API.

```lean
lemma affine_two_points_over_x_non2
    {P : (W⁄k).Point}
    (hPaff : P ≠ 0)
    (hP2 : 2 • P ≠ 0) :
    -- the fiber over x(P) has exactly two points, P and -P
```

Then the real division-polynomial theorem:

```lean
lemma preΨ'_rootSet_equiv_non2_nTorsion_mod_neg
    [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    -- roots of W.preΨ' n correspond to ±-orbits of
    -- affine n-torsion points with 2 • P ≠ 0
```

or avoid quotients and state the cardinal version directly:

```lean
lemma card_non2_nTorsion
    [IsSepClosed k] [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card {P : W.nTorsion n // 2 • (P : (W⁄k).Point) ≠ 0}
      =
    2 * ((n^2 - if Even n then 4 else 1) / 2)
```

This cardinal lemma packages correctness, separability, root counting, and the two-points-over-`x` argument.

Then the final theorem is just parity arithmetic:

```lean
theorem n_torsion_card
    [IsSepClosed k] [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (W.nTorsion n) = n^2 := by
  rcases Nat.even_or_odd n with hneven | hnodd
  · -- E[n] = E[2] disjoint union non-2 part
    -- card E[2] = 4
    -- card non-2 part = 2*((n^2 - 4)/2)
    omega
  · -- E[n] = {0} disjoint union nonzero/non-2 affine part
    -- card nonzero part = 2*((n^2 - 1)/2)
    omega
```

The `omega` arithmetic goals are:

```lean
1 + 2 * ((n^2 - 1) / 2) = n^2   -- odd n
4 + 2 * ((n^2 - 4) / 2) = n^2   -- even n
```

with the obvious side conditions.

---

## Bottom line

Mathlib’s current division-polynomial **degree** theory makes the leading-term part tractable. It does **not** yet make

```lean
Nat.card (E.nTorsion n) = n^2
```

a direct proof.

The missing theorem is not `Polynomial.card_roots` or `IsSepClosed`; those APIs are already good. The hard missing theorem is:

```lean
division polynomials correctly describe the kernel of [n],
and are separable when (n : k) ≠ 0.
```

Once you add that, the final cardinality proof is short and entirely standard.
