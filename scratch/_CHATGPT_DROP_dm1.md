# Q164 (dm1): general-`n` separability route choice

## Executive decision

For **fixed `n`**, the Sylvester/Bezout certificate route is excellent.  For example, `n = 3` is exactly the kind of finite certificate we already generated: compute

```text
A_n * preΨ'_n + B_n * derivative(preΨ'_n) = unit * Δ^e + Q * bRel
```

and finish in Lean by `linear_combination` plus `W.isUnit_Δ` and `(n : k) ≠ 0`.

For **general `n`**, I do **not** think the pure EDS-recurrence resultant route is the shorter formalization path in current Mathlib.  The decisive reason is that the EDS recurrence controls the values of the division-polynomial sequence, but separability is a statement about first-order variation in the `X`-coordinate.  The moment one differentiates the recurrence or evaluates it over dual numbers, one is proving that the infinitesimal kernel of `[n]` is zero when `(n : k) ≠ 0`; that is exactly the formal-group / separable-isogeny content.

So my route recommendation is:

```text
fixed small n:    polynomial Bezout certificates
all n:            geometric/formal-group infrastructure, or a theorem imported from it
```

I would not pivot the general-`n` theorem to a “pure EDS recurrence coprimality” proof unless someone already has a precise, published, recurrence-only discriminant/resultant theorem with a Lean-friendly induction.  I do not know such a theorem in a form that avoids torsion/formal-group content.

---

## (a) Is there a known closed-form resultant/discriminant proof?

There are classical and modern product/discriminant statements around division polynomials, but the ones I know or found are not the Lean shortcut we would need.

### What exists conceptually

For an elliptic curve over an algebraically closed field, the roots of the odd division polynomial are the `x`-coordinates of nonzero `n`-torsion points modulo `±1`.  Consequently, the discriminant of `ψ_n` is a product over pairs of distinct torsion points:

```text
Disc(ψ_n) = leadingCoeff(ψ_n)^(2d-2)
              * ∏_{P≠±Q} (x(P)-x(Q))^2.
```

Using addition formulas, Weil pairing, or invariant differentials, one can simplify such products to expressions involving powers of `n` and `Δ`.  But this is already torsion geometry: the proof knows that the roots are the torsion `x`-coordinates and that `[n]` is separable when `char ∤ n`.

### What is not available as a shortcut

I do **not** know a standard theorem of the following Lean-friendly form:

```text
Res_X(preΨ'_n, derivative(preΨ'_n))
  = ± n^a * Δ^b
```

proved solely from the `preNormEDS'` recurrence, uniformly in `n`, with explicit exponents and no appeal to torsion points, formal groups, or the multiplication-by-`n` morphism.

There are related papers, but they do not give the desired recurrence-only separability proof:

* Ward’s EDS theory gives the nonlinear recurrences and divisibility properties.  It does not by itself give derivative squarefreeness of the universal polynomial `preΨ'_n`.
* De Jong’s “One half log discriminant and division polynomials” studies discriminant/intersection phenomena using division-polynomial arithmetic.  It is related to products of division-polynomial values, especially at 2-torsion/branch points, but it is not a ready-made `Res(ψ_n, ψ_n')` certificate for all `n`.
* Homogeneous division polynomial constructions, such as Jin’s work, are useful for coordinate formulas for `[n]` over arbitrary rings; but the construction explicitly leans on geometric input such as the theorem of the cube.  That is much closer to the formal-group/group-scheme route than to a bare EDS recurrence proof.

So: a closed-form discriminant/resultant may exist in the literature in some normalization, but every route I know to it uses the geometry of torsion or `[n]`.  It is not a practical “avoid formal group” replacement.

---

## (b) Does Mathlib’s EDS recurrence carry enough structure?

Current Mathlib has the raw recurrence infrastructure:

```lean
preNormEDS'
preNormEDS'_zero
preNormEDS'_one
preNormEDS'_two
preNormEDS'_three
preNormEDS'_four
preNormEDS'_even
preNormEDS'_odd

WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
WeierstrassCurve.natDegree_preΨ'
WeierstrassCurve.leadingCoeff_preΨ'
WeierstrassCurve.preΨ'_ne_zero
```

This is enough for:

1. fixed-`n` expansion certificates;
2. degree/leading-coefficient computations;
3. special quotient/stratum recurrences, such as `Ψ₂Sq = 0` or `Ψ₃ = 0` rank-of-apparition lemmas;
4. proving values of the sequence after evaluation at a point, assuming some base nonvanishing facts.

It is **not** enough, by itself, to prove

```lean
IsCoprime (W.preΨ' n) (derivative (W.preΨ' n))
```

uniformly in `n`.

The obstruction is structural.  To prove squarefreeness by induction from the recurrence, one has to control common roots among all the neighboring factors appearing in

```lean
preΨ'_even
preΨ'_odd
```

and also control what happens after differentiating those recurrences.  A typical induction would need lemmas of the following strength:

```lean
IsCoprime (preΨ'_m) (preΨ'_r)       -- controlled by gcd(m,r)
IsCoprime (preΨ'_m) Ψ₂Sq            -- two-torsion exclusion
IsCoprime (preΨ'_m) Ψ₃/preΨ₄        -- small-stratum exclusions
no dual-number root of preΨ'_m      -- derivative/squarefreeness
```

The first three are already shadows of the torsion group law.  The last one is exactly the tangent/separable-isogeny statement.  Differentiating the EDS recurrence does not make it disappear; it reappears as the need to prove that the linearized recurrence has no nonzero solution at a root.  That is the formal tangent argument in coordinates.

In other words, a “pure EDS recurrence proof” would become a formal-group proof in disguise.  It may be possible, but it will be longer and more fragile than stating the geometric tangent lemma directly.

---

## Why fixed `n` and general `n` are fundamentally different

For fixed `n`, the problem is finite linear algebra:

```lean
-- Example shape for a fixed n:
private lemma bezout_preΨ'_n_dpreΨ'_n :
    A_n W * W.preΨ' n + B_n W * derivative (W.preΨ' n)
      = C (unit_scalar_n * W.Δ ^ e_n) := by
  linear_combination (norm := ring_nf) ...
```

A CAS can produce `A_n`, `B_n`, and `Q_n`.  Lean only checks a polynomial identity.

For general `n`, there is no finite certificate.  One needs a structural theorem explaining why **every** infinitesimal root is impossible.  That theorem is equivalent to one of:

```text
[n] is separable/étale when char ∤ n,
ker[n] is reduced,
the formal group satisfies [n](T) = n*T + O(T^2),
preΨ'_n has no dual-number roots with nonzero ε-coordinate.
```

Those are the same mathematical content in different languages.  General `n` is therefore substantially harder than any fixed `n` certificate.

---

## Direct route comparison

### Route P: polynomial + EDS recurrence coprimality

Target theorem:

```lean
theorem preΨ'_isCoprime_derivative_of_natCast_ne_zero
    {k : Type*} [Field k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)) := by
  -- hoped-for EDS recurrence induction
  sorry
```

What the induction would need:

```lean
-- pairwise rank-of-apparition/coprimality
lemma preΨ'_isCoprime_preΨ'_of_nat_coprime
    {m n : ℕ} (hmn : Nat.Coprime m n) :
    IsCoprime (W.preΨ' m) (W.preΨ' n) := by
  sorry

-- two-torsion exclusion
lemma preΨ'_isCoprime_Ψ₂Sq_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    IsCoprime (W.preΨ' n) W.Ψ₂Sq := by
  sorry

-- derivative induction, the hard part
lemma no_dual_root_preΨ'_of_natCast_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    ∀ {R}, SquareZeroExtension R → ... := by
  sorry
```

Assessment: this route is not actually independent of torsion geometry.  The pairwise coprimality and derivative induction encode the same rank-of-apparition and infinitesimal-kernel facts as the group law.  It is likely to sprawl into many recurrence-specific lemmas with difficult algebraic side conditions.

### Route G: geometric/formal group

Core theorem:

```lean
/-- Linear term of multiplication by `n` on the formal group of a Weierstrass curve. -/
theorem formalGroup_nsmul_linearCoeff
    (W : WeierstrassCurve k) (n : ℕ) :
    [n]_W(T) = C (n : k) * T + O(T^2) := by
  sorry
```

Then:

```lean
/-- On dual numbers, `[n]` acts on tangent vectors by scalar multiplication by `(n : k)`. -/
theorem formalGroup_nsmul_dual
    (W : WeierstrassCurve k) (n : ℕ) (v : k) :
    [n]_W(ε*v) = ε*((n : k) * v) := by
  sorry
```

And the desired separability follows from:

```lean
/-- A dual-number root of the division polynomial is an infinitesimal point in `ker[n]`. -/
theorem dual_root_preΨ'_mem_ker_nsmul
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} {x y dx dy : k}
    (h_curve_dual : /* (x+εdx,y+εdy) lies on W over k[ε] */)
    (h_non_two : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hψ : aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr dx) (W.preΨ' n) = 0) :
    /* translated tangent vector lies in infinitesimal ker [n] */ := by
  sorry
```

Assessment: this route requires new infrastructure, but the theorem is the standard one and the proof is conceptually linear.  It is the better route for **general `n`**.

---

## The single hardest missing step

The hardest missing step is not the Taylor expansion

```lean
aeval (x + ε*v) p = p.eval x + ε*v*p'.eval x
```

and not the scalar-injectivity conclusion

```lean
(n : k) * v = 0 → v = 0.
```

The hardest missing step is this bridge:

```lean
/-- Division-polynomial vanishing over dual numbers implies membership in the infinitesimal
kernel of multiplication by `n`. -/
theorem dual_root_preΨ'_mem_ker_nsmul
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} {x y dx dy : k}
    (hPε : /* dual-number point on W */)
    (h_non_two : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hpre : aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr dx) (W.preΨ' n) = 0) :
    /* [n](Pε) = O in the dual-number/functor-of-points sense */ := by
  sorry
```

This bridge needs either:

1. a group law/functor of points for Weierstrass curves over square-zero rings, or
2. homogeneous/projective division-polynomial formulas for `[n]` over arbitrary commutative rings.

Jin-style homogeneous division polynomials are relevant here: they provide coordinate polynomials for `[n]` over arbitrary rings, but formalizing them still uses substantial geometry or a large universal polynomial verification.

---

## Recommended Lean plan

I would split the project into two layers.

### Layer 1: keep fixed-`n` certificates for immediate local needs

Continue using CAS certificates for small `n`:

```lean
lemma preΨ'_three_separable ...
lemma preΨ'_four_separable ...
lemma preΨ'_five_separable ... -- only if specifically needed
```

This is cheap and reliable for finite cases.

### Layer 2: build the general geometric brick

Add a minimal formal-group file, not a full scheme theory at first:

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k] [DecidableEq k]

/-- A minimal local formal parameter at `O`, enough for dual numbers. -/
structure FormalTangentAtO (W : WeierstrassCurve k) where
  coeff : k

/-- Multiplication by `n` on the formal tangent line is scalar multiplication by `(n : k)`. -/
theorem formalTangentAtO_nsmul
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (v : FormalTangentAtO W) :
    -- exact statement should use the local formal group once defined
    True := by
  sorry

/-- Translate a non-2-torsion first-order deformation to the formal tangent at `O`. -/
theorem translate_dual_deformation_to_formal_tangent
    (W : WeierstrassCurve k) [W.IsElliptic]
    {x y dx dy : k}
    (hPε : /* dual-number curve equation */)
    (h_non_two : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    FormalTangentAtO W := by
  sorry

/-- Division-polynomial criterion over dual numbers, reduced away from the two-torsion factor. -/
theorem dual_root_preΨ'_mem_ker_nsmul
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} {x y dx dy : k}
    (hPε : /* dual-number point on W */)
    (h_non_two : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hpre : aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr dx) (W.preΨ' n) = 0) :
    True := by
  sorry

/-- General separability follows from the formal tangent theorem. -/
theorem preΨ'_separable_of_natCast_ne_zero
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Use `Polynomial.separable_def` or the dual-number multiple-root criterion.
  sorry

end

end WeierstrassCurve
```

This formal-tangent layer is the structural theorem.  Once it exists, the general separability statement is routine.

---

## Final recommendation

Do **not** bet the general theorem on a pure EDS recurrence proof unless a precise recurrence-only discriminant formula is supplied.  Fixed-`n` resultants are finite certificates; general-`n` separability is a structural theorem.  In Lean 4/current Mathlib, the most honest short path is:

```text
small n needed now  →  CAS Bezout certs
all n theorem       →  build minimal formal group / dual-number functor-of-points bridge
```

The general-`n` case is fundamentally harder than fixed `n`.  It is not “the same certificate with a parameter”; it is the separability of the multiplication-by-`n` morphism in disguise.
