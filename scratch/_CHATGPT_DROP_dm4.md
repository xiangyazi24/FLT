# Q2048 (dm4): Weil-pairing nondegeneracy and the `#E[m] = m^2` bottleneck

Date: 2026-06-28.

Question: for a Weierstrass curve `y^2 = x^3 + A*x + B`, can we prove nondegeneracy of the Weil pairing `e_m` by using:

1. `e_m` is alternating and bilinear;
2. over an algebraically closed field, `E[m]` is a free `ZMod m`-module of rank `2`;
3. a nondegenerate alternating form on `(ZMod m)^2` sends a basis pair to a primitive `m`-th root?

And, specifically, does Mathlib already have the hard step `#E[m] = m^2`; if not, can we axiomatize just that one fact and derive nondegeneracy?

## Executive answer

Mathlib does **not** appear to have the theorem

```lean
Nat.card E[m] = m ^ 2
```

for elliptic curves over an algebraically closed field.  Mathlib has substantial Weierstrass-curve point and division-polynomial infrastructure, including computed leading terms/degrees of division polynomials, but I did not find a completed torsion-cardinality theorem upstream.

The FLT project has exactly the expected scaffold in

```text
FLT/EllipticCurve/Torsion.lean
```

namely:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n

noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n)

theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry
```

So the fact is known to be the desired theorem, but in the FLT repo it is still a `sorry`, and I did not find it in Mathlib.

The important correction is: **axiomatizing only `#E[m] = m^2` is not enough to derive nondegeneracy of the actual Weil pairing.**  It is enough, in favorable cases, to help identify the group/module shape of `E[m]`, but nondegeneracy is an additional pairing-specific assertion.

## Why `#E[m] = m^2` alone is not enough

There are two separate issues.

### 1. For composite `m`, cardinality alone does not imply `E[m] ≃ (ZMod m)^2`

The type `E[m]` is killed by `m`, so it has exponent dividing `m`, and the desired cardinality is `m^2`.  But for composite `m`, a finite abelian group killed by `m` and of order `m^2` need not be `(ZMod m)^2`.

Example for `m = 4`:

```text
ZMod 4 × ZMod 2 × ZMod 2
```

has order `16 = 4^2` and is killed by `4`, but it is not free of rank `2` over `ZMod 4`.

This is exactly why the FLT scaffold’s group-theory lemma uses the stronger input

```lean
∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r
```

rather than only the single cardinality at `d = n`.  With cardinalities for all divisors of `n`, the finite abelian group structure can be forced into the expected `(ZMod n)^r` shape.

For prime `m = p`, the single fact `#E[p] = p^2` is much closer to enough for the group shape, because `E[p]` is an `𝔽_p`-vector space killed by `p`; cardinality `p^2` then says dimension `2`.  But for arbitrary `m`, one should axiomatize either all divisor-cardinality statements or directly the rank-two module equivalence.

### 2. Even if `E[m] ≃ (ZMod m)^2`, bilinear + alternating + cardinality does not imply nondegeneracy

A bilinear alternating pairing can be degenerate.  The zero pairing is the simplest example:

```text
e(P, Q) = 1
```

for all `P,Q`.  It is bilinear and alternating, and it can live on a group of size `m^2`, but it is maximally degenerate.

So the following implication is false:

```text
E[m] has m^2 points
+ e_m is bilinear and alternating
⇒ e_m is nondegenerate.
```

What is true is a pure algebra lemma of this shape:

```text
T ≃ (ZMod m)^2
+ e : T × T → μ_m is bilinear and alternating
+ e is nondegenerate
⇒ for any basis P,Q, e(P,Q) is a primitive m-th root.
```

The word “nondegenerate” in the premise is essential.  Cardinality by itself does not supply it.

## What can be safely axiomatized?

There are three levels of possible axioms, from weakest-useful to strongest.

### Option A: Axiomatize only the module structure of torsion

For pure algebra after the elliptic-curve geometry, use:

```lean
axiom elliptic_nTorsion_rank_two
    {k : Type*} [Field k] [IsSepClosed k]
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {m : ℕ} (hm : (m : k) ≠ 0) :
    Nonempty (E.nTorsion m ≃+ ZMod m × ZMod m)
```

This avoids proving division-polynomial point counting, but it still does **not** prove Weil-pairing nondegeneracy.  It only gives the domain shape needed for the final linear algebra.

### Option B: Axiomatize all divisor cardinalities, then derive the module structure

This matches the FLT scaffold better:

```lean
axiom elliptic_nTorsion_card_all_divisors
    {k : Type*} [Field k] [IsSepClosed k]
    (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]
    {m d : ℕ} (hd : d ∣ m) (hd_ne : (d : k) ≠ 0) :
    Nat.card (E.nTorsion d) = d ^ 2
```

Then, using a finite-abelian-group structure theorem, derive:

```lean
Nonempty (E.nTorsion m ≃+ ZMod m × ZMod m)
```

This is better than a single `#E[m] = m^2` axiom for composite `m`.

### Option C: Axiomatize the actual pairing nondegeneracy / primitive value

If the immediate Mazur-torsion goal only needs a primitive root of unity in the base field from full rational torsion, then the most economical seam is not the whole point-counting theorem.  It is a Weil-pairing consequence:

```lean
axiom weil_pairing_exists_primitive_value
    {k : Type*} [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) :
    ∃ P Q : E_m, IsPrimitiveRoot (weilPairing m P Q) m
```

or, even closer to the downstream use:

```lean
axiom full_rational_torsion_implies_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

This is essentially the current `weil_pairing_primitive_root` seam in the Mazur scaffold.  It bypasses the internal construction of `e_m` and focuses on the exact arithmetic consequence needed.

## Minimal theorem needed for the “basis maps to primitive root” step

Once one has an equivalence

```lean
T ≃+ ZMod m × ZMod m
```

and an alternating bilinear pairing

```lean
e : T → T → μ_m
```

then the standard pure group-theory theorem should be phrased as:

```text
If the left/right radical of e is trivial, and P,Q are a ZMod m-basis of T,
then e(P,Q) has order exactly m.
```

A skeletal mathematical proof:

* Let `ζ = e(P,Q)`.
* Bilinearity and alternation imply
  ```text
  e(aP + bQ, cP + dQ) = ζ^(a*d - b*c).
  ```
* If `ζ` has order `r < m`, then `rP` is nonzero in `ZMod m × ZMod m`, but it pairs trivially with both `P` and `Q`, hence with all of `T`.
* That contradicts nondegeneracy.
* Since the pairing values are `m`-th roots of unity, `orderOf ζ ∣ m`; therefore `orderOf ζ = m`, i.e. `ζ` is primitive.

This is a good pure-algebra lemma to formalize, but it requires nondegeneracy as input.  It does not prove nondegeneracy.

## Practical recommendation for dm4

Do **not** try to get Weil-pairing nondegeneracy from only:

```lean
Nat.card (E.nTorsion m) = m^2
```

That fact is too weak for composite `m`, and in any case it says nothing pairing-specific.

A clean formalization plan is:

1. Keep the current high-level axiom/consequence for the Mazur proof:
   ```lean
   full rational m-torsion ⇒ ∃ ζ : ℚ, IsPrimitiveRoot ζ m
   ```
2. Separately build pure algebra for alternating bilinear forms on `(ZMod m)^2`:
   ```lean
   nondegenerate alternating pairing ⇒ basis value primitive
   ```
3. For the elliptic curve geometry, choose one of these as the future hard seam:
   * `∀ d ∣ m, #E[d] = d^2`, enough for the module shape via finite abelian groups; plus
   * a genuine Weil-pairing nondegeneracy theorem, or directly a primitive-value theorem.

The most useful narrow axiom for replacing the geometric point-counting part is not just `#E[m] = m^2`; it is either:

```lean
Nonempty (E.nTorsion m ≃+ ZMod m × ZMod m)
```

or, if you want to keep the theorem close to the standard proof:

```lean
∀ d ∣ m, Nat.card (E.nTorsion d) = d^2
```

But the nondegeneracy of `e_m` still needs a separate pairing-specific input.
