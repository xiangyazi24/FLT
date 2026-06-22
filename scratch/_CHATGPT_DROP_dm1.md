# Q295-dm1: Ward theorem strategy for `IsEllSequence (normEDS b c d)`

## Executive summary

The cleanest formalization path is **not** to try to derive the full three-variable identity directly from the adjacent Somos relation by Gröbner reduction.  Your CAS result is the right diagnosis: the adjacent relation treats nearby sequence values as too free.  The proof must use the fact that `normEDS` is a globally generated sequence.

The most Lean-friendly route is:

1. Prove the **one-gap addition formula**

   ```text
   A(m,n) : W(m+n) W(m-n)
     = W(m+1) W(m-1) W(n)^2
       - W(n+1) W(n-1) W(m)^2.
   ```

   This is exactly `IsEllSequence W` with `r = 1` and `W(1)=1`.

2. Derive the full three-variable Ward identity from `A(m,n)` by a three-line algebraic cancellation-free calculation.

3. Prove `A(m,n)` by a **gap induction on `n`**, using product identities plus `normEDS_even`/`normEDS_odd`.  The induction steps are division-free after multiplying by a harmless square; over the universal ring one may cancel the square, then transport to any `CommRing` using `map_normEDS`.

This is closer to Ward/Shipsey than to a local Gröbner certificate, and it avoids building all of Stange's elliptic-net machinery.

---

## References and which is most formalization-friendly

* Morgan Ward, *Memoir on elliptic divisibility sequences*, Amer. J. Math. 70 (1948).  This is the original source for the addition law / Ward identity.
* Rachel Shipsey, *Elliptic Divisibility Sequences*, PhD thesis, 2000.  This is the most readable one-dimensional EDS reference for implementation.
* Katherine Stange, *Elliptic nets and elliptic curves*, 2007/2008.  This gives the clean conceptual recurrence

  ```text
  W(p+q+s)W(p-q)W(r+s)W(r)
  + W(q+r+s)W(q-r)W(p+s)W(p)
  + W(r+p+s)W(r-p)W(q+s)W(q) = 0.
  ```

  With `s = 0`, this is exactly Ward's three-variable identity, up to signs from `W(-n)=-W(n)`.

For Lean, the **Shipsey/Ward one-dimensional gap induction** is the shortest path.  Stange's elliptic nets are conceptually elegant, but formalizing net uniqueness and the full quartic recurrence is more infrastructure than needed for `normEDS`.

---

## Step 1: reduce the full identity to the `r = 1` identity

Let

```lean
def AddRel (W : ℤ → R) (m n : ℤ) : Prop :=
  W (m+n) * W (m-n)
    = W (m+1) * W (m-1) * W n ^ 2
      - W (n+1) * W (n-1) * W m ^ 2
```

Assume `AddRel W` holds for all pairs.  Then `IsEllSequence W` follows by pure algebra:

```lean
-- schematic Lean
lemma isEllSequence_of_addRel
    {R : Type*} [CommRing R]
    {W : ℤ → R}
    (hodd : ∀ n, W (-n) = - W n)
    (h1 : W 1 = 1)
    (hAdd : ∀ m n : ℤ,
      W (m+n) * W (m-n)
        = W (m+1) * W (m-1) * W n ^ 2
          - W (n+1) * W (n-1) * W m ^ 2) :
    IsEllSequence W := by
  intro m n r

  have hmr := hAdd m r
  have hnr := hAdd n r
  have hmn := hAdd m n

  -- Compute:
  -- W_n^2*(hAdd m r) - W_m^2*(hAdd n r)
  -- The `W_{r+1}W_{r-1} W_m^2 W_n^2` terms cancel.
  -- What remains is `W_r^2 * hAdd m n`.
  linear_combination (norm := ring_nf)
    W n ^ 2 * hmr - W m ^ 2 * hnr - W r ^ 2 * hmn
```

This reduction is important: it means the hard theorem is only the two-variable addition formula `A(m,n)`, not the full three-variable identity.

---

## Step 2: prove the two-variable addition formula by gap induction

Define

```lean
def S (W : ℤ → R) (m n : ℤ) : R := W (m+n) * W (m-n)
def B (W : ℤ → R) (i : ℤ) : R := W (i+1) * W (i-1)
```

The target is

```text
S(m,n) = B(m) W(n)^2 - B(n) W(m)^2.      (A(m,n))
```

You already have `A(m,2)` from `normEDS_adjacent_somos`.  The base gaps are:

```text
n = 0: trivial, since W(0)=0 and W(-i)=-W(i)
n = 1: trivial, since W(1)=1 and B(1)=W(2)W(0)=0
n = 2: your adjacent Somos theorem
n = 3,4: finite universal-ring certificates, or direct recurrences
```

Then use `normEDSRec` on the gap `n`.  The key is to prove even and odd gap steps from smaller gap formulas.  The clean step identities are below.

---

## Even gap step: from `n` to `2n`

The tautological product identity is

```text
W(m)^2 * S(m,2n) = S(m+n,n) * S(m-n,n).        (E-even-prod)
```

Indeed:

```text
S(m+n,n) = W(m+2n) W(m)
S(m-n,n) = W(m) W(m-2n).
```

Now use the induction hypothesis `A(_, n)` at centers `m+n` and `m-n`:

```text
S(m+n,n) = B(m+n) W(n)^2 - B(n) W(m+n)^2
S(m-n,n) = B(m-n) W(n)^2 - B(n) W(m-n)^2.
```

The only mixed product that appears is

```text
B(m+n) * B(m-n).
```

Rewrite it by regrouping as

```text
B(m+n) B(m-n)
  = S(m,n+1) * S(m,n-1).
```

Then use the induction hypotheses for gaps `n+1` and `n-1`:

```text
S(m,n+1) = B(m) W(n+1)^2 - B(n+1) W(m)^2
S(m,n-1) = B(m) W(n-1)^2 - B(n-1) W(m)^2.
```

Also use

```text
S(m,n) = B(m) W(n)^2 - B(n) W(m)^2.
```

After these substitutions, the right side of `(E-even-prod)` is a polynomial in

```text
W(n-2), W(n-1), W(n), W(n+1), W(n+2), W(m-1), W(m), W(m+1).
```

Using `normEDS_even` for `W(2n)` and `normEDS_odd` for `W(2n±1)`, `ring` proves

```text
S(m+n,n) S(m-n,n)
  = W(m)^2 * (B(m) W(2n)^2 - B(2n) W(m)^2).
```

Thus, over the universal domain, cancel `W(m)^2` to get `A(m,2n)`.  Then transport the resulting polynomial identity to an arbitrary `CommRing`.

### Lean theorem shape for the even step

```lean
-- Work first over the universal ring U = MvPolynomial (Fin 3) ℤ.
lemma addRel_even_gap_universal
    (m n : ℤ)
    (hm_nonzero : normEDS bU cU dU m ≠ 0)
    (h_n_minus : AddRel WU m (n-1))
    (h_n       : AddRel WU m n)
    (h_n_plus  : AddRel WU m (n+1))
    (h_center_plus  : AddRel WU (m+n) n)
    (h_center_minus : AddRel WU (m-n) n) :
    AddRel WU m (2*n) := by
  -- prove equality after multiplying by `W m ^ 2`
  have hmul : WU m ^ 2 * (lhs_minus_rhs_of_AddRel WU m (2*n)) = 0 := by
    linear_combination (norm := ring_nf)
      -- five AddRel hypotheses, plus recurrence expansions for W(2n), W(2n±1)
      ...
  exact sq_eq_zero_iff.mp?  -- no; use domain cancellation:
  exact mul_left_cancel₀ (sq_ne_zero hm_nonzero) hmul
```

In practice, do not expose `hm_nonzero` at every target.  Prove in the universal polynomial ring using a lemma:

```lean
normEDS_universal_ne_zero (i : ℤ) : normEDS bU cU dU i ≠ 0
```

then map the final polynomial identity to any `CommRing` using `map_normEDS`.

---

## Odd gap step: from `n,n+1` to `2n+1`

Use the product identity

```text
W(m-1)^2 * S(m,2n+1)
  = S(m+n,n+1) * S(m-n-1,n).       (E-odd-prod-left)
```

because

```text
S(m+n,n+1)   = W(m+2n+1) W(m-1)
S(m-n-1,n)   = W(m-1) W(m-2n-1).
```

There is also the symmetric version

```text
W(m+1)^2 * S(m,2n+1)
  = S(m+n+1,n) * S(m-n,n+1).       (E-odd-prod-right)
```

Use whichever square is nonzero in the universal ring.  For `m = 1`, the left square is `W(0)^2 = 0`, so use the right identity.  For `m = -1`, use the left identity.  For all other `m`, either works.

Substitute the induction hypotheses:

```text
A(m+n, n+1)
A(m-n-1, n)
```

and then regroup products like

```text
B(m+n) B(m-n-1)
```

into products of `S(m, n±something)` so that the already-known gap formulas apply.  After substitution, use `normEDS_odd` for `W(2n+1)` and `normEDS_even` for `W(2n)` and `W(2n+2)`.  A finite `ring` certificate proves the multiplied target, and universal-domain cancellation gives `A(m,2n+1)`.

### Lean theorem shape for the odd step

```lean
lemma addRel_odd_gap_universal_left
    (m n : ℤ)
    (hm1_nonzero : normEDS bU cU dU (m-1) ≠ 0)
    (h₁ : AddRel WU (m+n) (n+1))
    (h₂ : AddRel WU (m-n-1) n)
    -- plus the gap formulas needed after regrouping
    : AddRel WU m (2*n+1) := by
  have hmul : WU (m-1)^2 * lhs_minus_rhs_of_AddRel WU m (2*n+1) = 0 := by
    linear_combination (norm := ring_nf) ...
  exact mul_left_cancel₀ (sq_ne_zero hm1_nonzero) hmul
```

For the exceptional center `m = 1`, use the right-product version with `W(m+1)=W(2)=b`, nonzero in the universal polynomial ring.

---

## Why universal ring transport is the cleanest way

The multiplied identities above require cancellation by `W(m)^2`, `W(m-1)^2`, or `W(m+1)^2`.  Cancellation is not valid in an arbitrary `CommRing`.  But the theorem is a universal polynomial identity in the initial values `(b,c,d)`.  Therefore:

1. Prove the identity over

   ```lean
   U := MvPolynomial (Fin 3) ℤ
   bU := MvPolynomial.X 0
   cU := MvPolynomial.X 1
   dU := MvPolynomial.X 2
   ```

   where `U` is an integral domain.

2. Cancel nonzero universal EDS terms there.

3. Transport the resulting equality to any `CommRing R` by the ring hom

   ```lean
   MvPolynomial.aeval ![b,c,d] : U →+* R
   ```

   and Mathlib's theorem

   ```lean
   map_normEDS
   ```

This is exactly the pattern you already used successfully for the adjacent relation.

The one extra universal lemma needed is:

```lean
lemma normEDS_universal_ne_zero (n : ℤ) :
    normEDS bU cU dU n ≠ 0
```

A practical proof is by specialization: map `bU,cU,dU` to a concrete numerical EDS over `ℤ`, for example choose values for which many initial terms are nonzero and prove the image of the desired term is nonzero.  For all `n`, however, this requires a family.  A better proof is by leading monomial/degree induction using `normEDS_even`/`normEDS_odd`.

If this nonzero lemma becomes a bottleneck, avoid cancellation by keeping both left and right multiplied odd/even identities and combining them using adjacent relations.  That is more algebra but works over `CommRing` directly.

---

## Does `complEDS` help?

`complEDS` materially helps with the divisibility half:

```text
W(k) ∣ W(nk)
```

because it gives a witness

```lean
normEDS b c d k * complEDS b c d k n = normEDS b c d (n*k).
```

It does **not** by itself prove the full Ward addition law.  Divisibility controls multiples of one index; Ward's relation controls three independent indices and is an addition/subtraction formula.  There is no known finite transfer

```text
divisibility + adjacent Somos  ⇒  full IsEllSequence
```

without essentially rebuilding the global addition-law induction above.

So use `complEDS` for `IsDivSequence`.  Do not expect it to shorten the proof of `IsEllSequence`, except perhaps as a convenience for special cases where one index divides another.

---

## Is there a slicker universal-ring or sigma-function route?

There are two slick conceptual routes, but neither is shorter in current Lean.

### 1. Elliptic nets

Define a rank-one elliptic net as a function `W : ℤ → R` satisfying Stange's quartic recurrence:

```text
W(p+q+s)W(p-q)W(r+s)W(r)
+ W(q+r+s)W(q-r)W(p+s)W(p)
+ W(r+p+s)W(r-p)W(q+s)W(q) = 0.
```

Then `IsEllSequence` is the case `s = 0`.  Prove that `normEDS` is the unique normalized rank-one elliptic net with values `0,1,b,c,d*b` at `0,1,2,3,4`.  This is Stange's clean theory.

Formalization cost: new net definitions, uniqueness theorem, and a nontrivial recurrence induction.  Conceptually beautiful, but probably more infrastructure than the Ward one-dimensional proof.

### 2. Sigma-function / elliptic-curve origin

Construct `normEDS` from a Weierstrass sigma function or from actual division polynomials and derive Ward's identity from the group law.  Then prove the recursive `normEDS` agrees with that construction by uniqueness.

Formalization cost: formal groups/sigma functions/division-polynomial correctness.  This is much larger than the EDS recurrence proof.

### 3. Universal ring with divisor/degree argument

Prove identities in `ℤ[b,c,d]` by showing a universal polynomial vanishes on enough specializations, or by degree plus divisibility arguments.  This can work for finite local identities, but the full family still needs induction to avoid infinitely many separate certificates.

So the practical route remains:

```text
universal ring + gap induction + map_normEDS transport.
```

---

## Recommended formalization outline

```lean
namespace FLT.EDS.Ward

abbrev U := MvPolynomial (Fin 3) ℤ

def bU : U := MvPolynomial.X 0
def cU : U := MvPolynomial.X 1
def dU : U := MvPolynomial.X 2

def WU : ℤ → U := normEDS bU cU dU

def B (W : ℤ → R) (i : ℤ) : R := W (i+1) * W (i-1)
def S (W : ℤ → R) (m n : ℤ) : R := W (m+n) * W (m-n)

def AddRel (W : ℤ → R) (m n : ℤ) : Prop :=
  S W m n = B W m * W n^2 - B W n * W m^2

lemma isEllSequence_of_AddRel
    {W : ℤ → R}
    (hAdd : ∀ m n, AddRel W m n) :
    IsEllSequence W := by
  intro m n r
  linear_combination (norm := ring_nf)
    W n^2 * hAdd m r - W m^2 * hAdd n r - W r^2 * hAdd m n

-- Universal proof of AddRel by gap induction.
theorem universal_AddRel : ∀ m n : ℤ, AddRel WU m n := by
  -- prove by induction on `n.natAbs`, using even/odd gap steps above
  sorry

-- Transport to arbitrary CommRing.
theorem addRel_normEDS {R : Type*} [CommRing R]
    (b c d : R) :
    ∀ m n : ℤ, AddRel (normEDS b c d) m n := by
  intro m n
  -- apply `MvPolynomial.aeval ![b,c,d]` to `universal_AddRel m n`
  -- use `map_normEDS`
  sorry

theorem isEllSequence_normEDS {R : Type*} [CommRing R]
    (b c d : R) :
    IsEllSequence (normEDS b c d) :=
  isEllSequence_of_AddRel (addRel_normEDS b c d)

end FLT.EDS.Ward
```

---

## The crux to implement next

The exact next lemma is the even gap step in the universal ring:

```lean
lemma universal_AddRel_even_gap
    (m n : ℤ)
    (h_nm1 : AddRel WU m (n-1))
    (h_n   : AddRel WU m n)
    (h_np1 : AddRel WU m (n+1))
    (h_center_plus  : AddRel WU (m+n) n)
    (h_center_minus : AddRel WU (m-n) n) :
    AddRel WU m (2*n)
```

The proof is:

```text
1. prove W(m)^2 * target = 0 using the product identity
   W(m)^2 S(m,2n) = S(m+n,n) S(m-n,n),
   the five AddRel hypotheses, and normEDS_even/odd for W(2n), W(2n±1);
2. cancel W(m)^2 in the universal domain.
```

Then implement the odd gap analogue with the `W(m-1)^2` / `W(m+1)^2` product identities.

That is the cleanest induction structure I know for Lean: finite algebraic step certificates, no Chabauty-style machinery, no elliptic curves, and only one universal-ring transport theorem.