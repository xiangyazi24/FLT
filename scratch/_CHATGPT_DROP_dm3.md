# Q312 (dm3): `normEDS` nonvanishing by a weighted/lex leading term

This is the concrete approach I would use for

```lean
normEDS b c d j ≠ 0
```

in `ℤ[b,c,d] = MvPolynomial (Fin 3) ℤ`, with

```lean
W 0 = 0,  W 1 = 1,  W 2 = b,  W 3 = c,  W 4 = b*d
```

and Ward recurrences

```lean
normEDS_even :
  W (2*m) * b =
    W (m-1)^2 * W m * W (m+2)
      - W (m-2) * W m * W (m+1)^2

normEDS_odd :
  W (2*m+1) =
    W (m+2) * W m^3
      - W (m-1) * W (m+1)^3
```

The right answer is **not** a plain scalar weight.  Use the natural scalar weight only as the first component, then break ties lexicographically.

## 1. Term order / grading choice

Give the variables the primary weights

```text
wt₀(b) = 3,   wt₀(c) = 8,   wt₀(d) = 12.
```

For a monomial `b^β c^γ d^δ`, define

```text
wt₀(β,γ,δ) = 3β + 8γ + 12δ.
```

Then refine this by the lexicographic key

```text
K(β,γ,δ) = (wt₀(β,γ,δ), -β, -γ, -δ),
```

ordered lexicographically, with larger `K` better.  Equivalently:

1. maximize the primary weight `wt₀`;
2. among equal primary weights, minimize the `b`-exponent;
3. among those, minimize the `c`-exponent;
4. among those, minimize the `d`-exponent.

This is the important point: the scalar weight `(3,8,12)` makes the polynomials homogeneous, so it does **not** by itself separate the two recurrence summands.  The lex refinement is what prevents cancellation.

For finite supports, this key is enough.  It is additive/translation-invariant:

```text
K(u) < K(v)  ⇒  K(u+w) < K(v+w),
```

so the selected term of a product is the product of the selected terms, provided both selected terms are unique.

## 2. Main leading-term statement

For `n ≥ 1`, the `K`-leading term of `W n` is as follows.

For odd indices, with `n = 2r+1`, `r ≥ 0`:

```text
LT_K(W(2r+1)) = (-1)^(⌊r/2⌋) · c^(r(r+1)/2).
```

For even indices, with `n = 2r`, `r ≥ 1`:

```text
LT_K(W(2r)) = (-1)^(⌊(r-1)/2⌋) · b · c^((r-1)(r-2)/2) · d^(r-1).
```

Equivalently, if

```text
ε_n = (-1)^(⌊(n-1)/4⌋),
```

then the coefficient is always `ε_n`, and the exponent vector is

```text
E(2r+1) = (0, r(r+1)/2, 0),
E(2r)   = (1, (r-1)(r-2)/2, r-1).
```

The primary top degree is

```text
wt₀(E(n)) = n^2 - 1.
```

Indeed:

```text
wt₀(E(2r+1)) = 8 · r(r+1)/2 = 4r(r+1) = (2r+1)^2 - 1,

wt₀(E(2r)) = 3 + 8 · (r-1)(r-2)/2 + 12(r-1)
            = 4r^2 - 1
            = (2r)^2 - 1.
```

Small checks:

```text
W5 = b^4 d - c^3,
LT_K(W5) = -c^3.

W6 = b^5 c d - b c^4 - b c d^2,
LT_K(W6) = -b c d^2.

W7 = b^4 c^3 d - b^4 d^3 - c^6,
LT_K(W7) = -c^6.

W8 = -b^9 d^3 + 3b^5 c^3 d^2 - 2b c^6 d - b c^3 d^3,
LT_K(W8) = -b c^3 d^3.
```

All four examples have primary degree `n^2-1`; the lex tie-breaker picks the displayed term.

## 3. Why pure scalar weights tie

The weight `(3,8,12)` is forced if one wants the expected quadratic degree and the base values

```text
deg W2 = deg b = 3,
deg W3 = deg c = 8,
deg W4 = deg(bd) = 15.
```

It gives `deg Wn = n^2-1`.  But then both products in each Ward recurrence have the same primary degree.

Odd recurrence:

```text
wt₀(W(m+2) W(m)^3)
  = ((m+2)^2-1) + 3(m^2-1)
  = 4m^2 + 4m,

wt₀(W(m-1) W(m+1)^3)
  = ((m-1)^2-1) + 3((m+1)^2-1)
  = 4m^2 + 4m.
```

Even recurrence, before division by `b`:

```text
wt₀(W(m-1)^2 W(m) W(m+2))
  = 2((m-1)^2-1) + (m^2-1) + ((m+2)^2-1)
  = 4m^2 + 2,

wt₀(W(m-2) W(m) W(m+1)^2)
  = ((m-2)^2-1) + (m^2-1) + 2((m+1)^2-1)
  = 4m^2 + 2.
```

Since multiplying by `b` adds primary degree `3`, this is exactly

```text
((2m)^2 - 1) + 3.
```

So the scalar weight gives the right degree but cannot prove noncancellation.  The lex tie-breaker is essential.

## 4. Induction proof of the leading term

Write

```text
M_n = E(n),
λ_n = ε_n.
```

The induction hypothesis is:

```text
W_n has unique K-leading monomial b^(M_n.b) c^(M_n.c) d^(M_n.d)
with coefficient λ_n = ±1.
```

The product lemma says that, if `p` and `q` have unique `K`-leading exponents `u` and `v` with coefficients `a` and `b`, then `p*q` has unique `K`-leading exponent `u+v` with coefficient `a*b`.  This is where additivity of `K` is used.

The sum/difference lemma says that, if the leading exponents of two terms have strictly different `K`-keys, then the larger one remains the unique leading term of the sum or difference.

### Odd recurrence

Let `n = 2m+1`.

#### Case `m = 2r`, so `n = 4r+1`

The two candidate leading exponents are

```text
A = M_(2r+2) + 3 M_(2r),
B = M_(2r-1) + 3 M_(2r+1).
```

They have the same primary weight, but their `b`-exponents are

```text
A.b = 4,
B.b = 0.
```

Because the tie-breaker minimizes the `b`-exponent, `B` is strictly larger in the `K` order.  Thus the leading term comes from the second recurrence summand, with the minus sign:

```text
LT_K(W(4r+1))
  = - LT_K(W(2r-1)) · LT_K(W(2r+1))^3
  = (-1)^r · c^(r(2r+1)).
```

This agrees with the formula for `2s+1 = 4r+1`, namely `s=2r` and

```text
s(s+1)/2 = (2r)(2r+1)/2 = r(2r+1).
```

The sign check is

```text
- ε_(2r-1) ε_(2r+1)^3 = ε_(4r+1),
```

which reduces to

```text
1 + ⌊(r-1)/2⌋ + ⌊r/2⌋ = r.
```

#### Case `m = 2r+1`, so `n = 4r+3`

The two candidate leading exponents are

```text
A = M_(2r+3) + 3 M_(2r+1),
B = M_(2r)   + 3 M_(2r+2).
```

Again the primary weights tie, but now

```text
A.b = 0,
B.b = 4.
```

So `A` is strictly larger.  The leading term comes from the first recurrence summand:

```text
LT_K(W(4r+3))
  = LT_K(W(2r+3)) · LT_K(W(2r+1))^3
  = (-1)^r · c^((r+1)(2r+1)).
```

This agrees with `2s+1 = 4r+3`, where `s=2r+1`:

```text
s(s+1)/2 = (2r+1)(2r+2)/2 = (2r+1)(r+1).
```

The sign check is

```text
ε_(2r+3) ε_(2r+1)^3 = ε_(4r+3),
```

using

```text
⌊(r+1)/2⌋ + ⌊r/2⌋ = r.
```

### Even recurrence

Let `n = 2m`.  The recurrence gives the leading term of `W(2m) * b`.  After finding it, subtract one `b` from the exponent vector to get the leading term of `W(2m)`.

#### Case `m = 2r`, so `n = 4r`, `r ≥ 2`

The two candidate leading exponents before division by `b` are

```text
A = 2 M_(2r-1) + M_(2r) + M_(2r+2),
B = M_(2r-2) + M_(2r) + 2 M_(2r+1).
```

Their primary weights tie and their `b`-exponents tie:

```text
A.b = B.b = 2.
```

The `c`-exponents are

```text
A.c = (r-1)(2r-1),
B.c = (r-1)(2r-1) + 3.
```

So `A` is strictly larger because the tie-breaker minimizes the `c`-exponent.  Hence

```text
LT_K(W(4r) * b)
  = LT_K(W(2r-1))^2 · LT_K(W(2r)) · LT_K(W(2r+2)).
```

The exponent of this term is

```text
(2, (r-1)(2r-1), 2r-1).
```

Dividing by the extra `b` gives

```text
M_(4r) = (1, (r-1)(2r-1), 2r-1),
```

which is the even formula with `4r = 2s`, `s=2r`:

```text
((s-1)(s-2)/2, s-1)
  = ((2r-1)(2r-2)/2, 2r-1)
  = ((r-1)(2r-1), 2r-1).
```

The sign check is

```text
ε_(2r-1)^2 ε_(2r) ε_(2r+2) = ε_(4r),
```

using

```text
⌊(2r-1)/4⌋ + ⌊(2r+1)/4⌋ = r-1.
```

#### Case `m = 2r+1`, so `n = 4r+2`, `r ≥ 1`

The two candidate leading exponents before division by `b` are

```text
A = 2 M_(2r) + M_(2r+1) + M_(2r+3),
B = M_(2r-1) + M_(2r+1) + 2 M_(2r+2).
```

Again the primary weights tie and the `b`-exponents tie:

```text
A.b = B.b = 2.
```

The `c`-exponents are

```text
A.c = 2r^2 - r + 3,
B.c = 2r^2 - r.
```

So `B` is strictly larger.  Since `B` comes from the second recurrence summand, the recurrence contributes the extra minus sign:

```text
LT_K(W(4r+2) * b)
  = - LT_K(W(2r-1)) · LT_K(W(2r+1)) · LT_K(W(2r+2))^2.
```

The exponent before division by `b` is

```text
(2, 2r^2-r, 2r).
```

Dividing by `b` gives

```text
M_(4r+2) = (1, 2r^2-r, 2r),
```

which is the even formula with `4r+2 = 2s`, `s=2r+1`:

```text
((s-1)(s-2)/2, s-1)
  = ((2r)(2r-1)/2, 2r)
  = (2r^2-r, 2r).
```

The sign check is

```text
- ε_(2r-1) ε_(2r+1) ε_(2r+2)^2 = ε_(4r+2),
```

using

```text
1 + ⌊(r-1)/2⌋ + ⌊r/2⌋ = r.
```

This completes the positive-index induction.  Since every displayed leading coefficient is `±1`, each `W n` for `n ≥ 1` is nonzero.  Negative indices then follow from the usual oddness lemma for Ward EDS:

```lean
-- expected shape; use the actual theorem name in the file
normEDS_neg : W (-n) = - W n
```

so `W j ≠ 0` for every integer `j ≠ 0`.

## 5. Lean formalization skeleton

I would not start with `MvPolynomial.degrees` or `totalDegree`.  They lose exactly the tie-breaker that matters here.  The most direct route is a small custom leading-term predicate using `MvPolynomial.support` and `MvPolynomial.coeff`.

### Basic setup

```lean
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

open scoped BigOperators
open MvPolynomial

abbrev R := MvPolynomial (Fin 3) ℤ
abbrev Exp := (Fin 3 →₀ ℕ)

-- variable indices: 0=b, 1=c, 2=d
noncomputable abbrev bVar : R := X (0 : Fin 3)
noncomputable abbrev cVar : R := X (1 : Fin 3)
noncomputable abbrev dVar : R := X (2 : Fin 3)

abbrev eb : Exp := Finsupp.single (0 : Fin 3) 1
abbrev ec : Exp := Finsupp.single (1 : Fin 3) 1
abbrev ed : Exp := Finsupp.single (2 : Fin 3) 1
```

### The key order

It is simpler to define the comparison predicate directly than to instantiate a global monomial order.

```lean
def wt0 (e : Exp) : ℕ :=
  3 * e (0 : Fin 3) + 8 * e (1 : Fin 3) + 12 * e (2 : Fin 3)

/-- `KeyLE u v` means `u` is no better than `v` for the key
`(wt0, -bExp, -cExp, -dExp)`. -/
def KeyLE (u v : Exp) : Prop :=
  wt0 u < wt0 v ∨
  wt0 u = wt0 v ∧
    (v (0 : Fin 3) < u (0 : Fin 3) ∨
     v (0 : Fin 3) = u (0 : Fin 3) ∧
       (v (1 : Fin 3) < u (1 : Fin 3) ∨
        v (1 : Fin 3) = u (1 : Fin 3) ∧
          v (2 : Fin 3) ≤ u (2 : Fin 3)))

def KeyLT (u v : Exp) : Prop := KeyLE u v ∧ ¬ KeyLE v u

lemma KeyLE_refl (u : Exp) : KeyLE u u := by
  unfold KeyLE
  right
  constructor · rfl
  right
  constructor · rfl
  right
  constructor · rfl
  exact le_rfl

lemma KeyLE_add_right {u v w : Exp} (h : KeyLE u v) :
    KeyLE (u + w) (v + w) := by
  -- Unfold `KeyLE`; use `simp [wt0, Finsupp.add_apply]` and `omega`.
  -- This is the translation-invariance of the key.
  sorry

lemma KeyLT_add_right {u v w : Exp} (h : KeyLT u v) :
    KeyLT (u + w) (v + w) := by
  -- From `KeyLE_add_right` in both directions.
  sorry
```

In practice I would add symmetric `add_left` lemmas and an `nsmul` version:

```lean
lemma KeyLE_add_left {u v w : Exp} (h : KeyLE u v) :
    KeyLE (w + u) (w + v) := by
  simpa [add_comm, add_left_comm, add_assoc] using KeyLE_add_right (w := w) h

lemma KeyLT_add_left {u v w : Exp} (h : KeyLT u v) :
    KeyLT (w + u) (w + v) := by
  simpa [add_comm, add_left_comm, add_assoc] using KeyLT_add_right (w := w) h
```

### Leading-term predicate

```lean
/-- `HasLead p e a` says that the unique `K`-leading monomial of `p`
has exponent `e` and coefficient `a`. -/
def HasLead (p : R) (e : Exp) (a : ℤ) : Prop :=
  coeff e p = a ∧
  a ≠ 0 ∧
  ∀ f : Exp, coeff f p ≠ 0 → f ≠ e → KeyLT f e

lemma HasLead.ne_zero {p : R} {e : Exp} {a : ℤ}
    (h : HasLead p e a) : p ≠ 0 := by
  intro hp
  rcases h with ⟨hcoeff, hane, _⟩
  have : coeff e p = 0 := by simp [hp]
  exact hane (by simpa [hcoeff] using this.symm)

lemma HasLead_C_one : HasLead (1 : R) 0 1 := by
  -- `simp [HasLead]`; for the last field use `coeff f 1 ≠ 0` implies `f=0`.
  sorry

lemma HasLead_X (i : Fin 3) :
    HasLead (X i : R) (Finsupp.single i 1) 1 := by
  -- `simp [HasLead]` plus `coeff_X`/support facts.
  sorry

lemma HasLead_monomial {e : Exp} {a : ℤ} (ha : a ≠ 0) :
    HasLead (monomial e a : R) e a := by
  -- Useful for `b*d` if you prefer not to multiply the two `X` leads.
  sorry
```

The important algebraic lemmas are the following.

```lean
lemma HasLead_neg {p : R} {e : Exp} {a : ℤ}
    (hp : HasLead p e a) : HasLead (-p) e (-a) := by
  -- coefficients are negated; support/key comparison unchanged.
  sorry

lemma HasLead_mul {p q : R} {ep eq : Exp} {ap aq : ℤ}
    (hp : HasLead p ep ap) (hq : HasLead q eq aq) :
    HasLead (p * q) (ep + eq) (ap * aq) := by
  -- Use `coeff_mul`, or the support-of-product API.
  -- If a product monomial has maximal key, both factors must have maximal key;
  -- uniqueness then forces `ep` and `eq`.
  -- Coefficient at `ep+eq` is therefore `ap*aq`.
  sorry

lemma HasLead_pow {p : R} {e : Exp} {a : ℤ} (hp : HasLead p e a) :
    ∀ k : ℕ, HasLead (p^k) (k • e) (a^k)
  | 0 => by simpa using HasLead_C_one
  | k+1 => by
      simpa [pow_succ, Nat.succ_nsmul] using HasLead_mul hp (HasLead_pow hp k)

lemma HasLead_sub_of_left {p q : R} {ep eq : Exp} {ap aq : ℤ}
    (hp : HasLead p ep ap) (hq : HasLead q eq aq)
    (hkey : KeyLT eq ep) :
    HasLead (p - q) ep ap := by
  -- The top key of `q` is strictly below the top key of `p`, so no cancellation.
  -- Use `coeff_sub`.
  sorry

lemma HasLead_sub_of_right {p q : R} {ep eq : Exp} {ap aq : ℤ}
    (hp : HasLead p ep ap) (hq : HasLead q eq aq)
    (hkey : KeyLT ep eq) :
    HasLead (p - q) eq (-aq) := by
  -- Same, but the dominant term comes from `-q`.
  sorry
```

For the even recurrence, add the shift lemma for multiplication by `b`.

```lean
lemma HasLead_mul_b_iff {p : R} {e : Exp} {a : ℤ} :
    HasLead (p * bVar) (e + eb) a ↔ HasLead p e a := by
  -- Coefficients of `p * X 0` are coefficients of `p` with the exponent shifted by `eb`.
  -- This is just the monomial multiplication coefficient formula.
  sorry
```

If the available API makes the iff annoying, prove only the direction needed:

```lean
lemma HasLead_of_mul_b {p : R} {e : Exp} {a : ℤ}
    (h : HasLead (p * bVar) (e + eb) a) : HasLead p e a := by
  sorry
```

### Closed-form exponent and sign

```lean
def tri (r : ℕ) : ℕ := r * (r + 1) / 2

def eOdd (r : ℕ) : Exp :=
  Finsupp.single (1 : Fin 3) (tri r)

def eEven (r : ℕ) : Exp :=
  Finsupp.single (0 : Fin 3) 1 +
  Finsupp.single (1 : Fin 3) ((r - 1) * (r - 2) / 2) +
  Finsupp.single (2 : Fin 3) (r - 1)

def epsNat (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ ((n - 1) / 4)

lemma eps_odd (r : ℕ) : epsNat (2*r+1) = (-1 : ℤ) ^ (r / 2) := by
  unfold epsNat
  -- arithmetic: `(2*r+1-1)/4 = r/2`
  congr
  omega

lemma eps_even (r : ℕ) (hr : 1 ≤ r) :
    epsNat (2*r) = (-1 : ℤ) ^ ((r - 1) / 2) := by
  unfold epsNat
  -- arithmetic: `(2*r-1)/4 = (r-1)/2` for `r ≥ 1`
  congr
  omega
```

Top primary degree lemmas:

```lean
lemma wt0_eOdd (r : ℕ) : wt0 (eOdd r) = (2*r+1)^2 - 1 := by
  unfold wt0 eOdd tri
  -- Use `omega`/`nlinarith` after clearing the `/2`; this is elementary.
  sorry

lemma wt0_eEven (r : ℕ) (hr : 1 ≤ r) : wt0 (eEven r) = (2*r)^2 - 1 := by
  unfold wt0 eEven
  -- Again elementary arithmetic.
  sorry
```

The exact arithmetic lemmas that separate the recurrence terms are best written as four small named lemmas.

```lean
lemma odd_even_m_dominates_second (r : ℕ) (hr : 1 ≤ r) :
    KeyLT (eEven (r+1) + 3 • eEven r)
          (eOdd (r-1) + 3 • eOdd r) := by
  -- This is the `m=2r`, `n=4r+1` case.
  -- Both primary degrees tie; b-exponents are `4` and `0`.
  sorry

lemma odd_odd_m_dominates_first (r : ℕ) (hr : 1 ≤ r) :
    KeyLT (eEven r + 3 • eEven (r+1))
          (eOdd (r+1) + 3 • eOdd r) := by
  -- This is the `m=2r+1`, `n=4r+3` case.
  -- Both primary degrees tie; b-exponents are `4` and `0`.
  sorry

lemma even_even_m_dominates_first (r : ℕ) (hr : 2 ≤ r) :
    KeyLT (eEven (r-1) + eEven r + 2 • eOdd r)
          (2 • eOdd (r-1) + eEven r + eEven (r+1)) := by
  -- This is the `m=2r`, `n=4r` case.
  -- Primary and b-exponents tie; c-exponents differ by `3`.
  sorry

lemma even_odd_m_dominates_second (r : ℕ) (hr : 1 ≤ r) :
    KeyLT (2 • eEven r + eOdd r + eOdd (r+1))
          (eOdd (r-1) + eOdd r + 2 • eEven (r+1)) := by
  -- This is the `m=2r+1`, `n=4r+2` case.
  -- Primary and b-exponents tie; c-exponents differ by `3`.
  sorry
```

Depending on how you normalize `nsmul` and addition of `Finsupp`s, you may want to state these with the terms expanded exactly as they appear in the recurrence.  They should all reduce to `omega`/`nlinarith` after unfolding `eOdd`, `eEven`, `tri`, `wt0`, and `KeyLE`.

### Induction theorem

The cleanest statement is a positive-index theorem, then a wrapper for integers.

```lean
-- Replace this with the actual local abbreviation for `normEDS b c d`.
noncomputable abbrev W (n : ℤ) : R :=
  normEDS bVar cVar dVar n

def topExp : ℕ → Exp
  | 0 => 0
  | n+1 =>
      if h : ∃ r, n+1 = 2*r+1 then
        eOdd (Nat.find h)
      else
        -- In production, avoid this awkward definition; prove separate odd/even theorems.
        0
```

In practice I would avoid a single `topExp` definition and prove separate mutually convenient theorem shapes:

```lean
theorem hasLead_odd_even :
    (∀ r : ℕ, HasLead (W (Int.ofNat (2*r+1)))
        (eOdd r) ((-1 : ℤ) ^ (r / 2))) ∧
    (∀ r : ℕ, 1 ≤ r → HasLead (W (Int.ofNat (2*r)))
        (eEven r) ((-1 : ℤ) ^ ((r - 1) / 2))) := by
  -- Use strong induction on `n`, or two theorems proved by strong induction on the index.
  -- Base cases:
  --   W1 = 1      -> eOdd 0, coeff +1
  --   W2 = b      -> eEven 1, coeff +1
  --   W3 = c      -> eOdd 1, coeff +1
  --   W4 = b*d    -> eEven 2, coeff +1
  -- Inductive cases:
  --   n=4r+1: `normEDS_odd` with m=2r, use `HasLead_sub_of_right`.
  --   n=4r+3: `normEDS_odd` with m=2r+1, use `HasLead_sub_of_left`.
  --   n=4r:   `normEDS_even` with m=2r, prove lead of RHS, then `HasLead_of_mul_b`.
  --   n=4r+2: `normEDS_even` with m=2r+1, prove lead of RHS, then `HasLead_of_mul_b`.
  sorry
```

A more explicit sketch of the `4r+1` branch:

```lean
-- n = 4*r+1, r ≥ 1
have hA : HasLead
    (W (Int.ofNat (2*r+2)) * W (Int.ofNat (2*r))^3)
    (eEven (r+1) + 3 • eEven r)
    (((-1 : ℤ) ^ (r / 2)) * (((-1 : ℤ) ^ ((r-1)/2))^3)) := by
  -- `HasLead_mul`, `HasLead_pow`, induction hypotheses.
  sorry

have hB : HasLead
    (W (Int.ofNat (2*r-1)) * W (Int.ofNat (2*r+1))^3)
    (eOdd (r-1) + 3 • eOdd r)
    (((-1 : ℤ) ^ ((r-1)/2)) * (((-1 : ℤ) ^ (r/2))^3)) := by
  sorry

have hdom : KeyLT (eEven (r+1) + 3 • eEven r)
                  (eOdd (r-1) + 3 • eOdd r) :=
  odd_even_m_dominates_second r ‹1 ≤ r›

have hlead : HasLead
    (W (Int.ofNat (2*r+2)) * W (Int.ofNat (2*r))^3
      - W (Int.ofNat (2*r-1)) * W (Int.ofNat (2*r+1))^3)
    (eOdd (r-1) + 3 • eOdd r)
    (- (((-1 : ℤ) ^ ((r-1)/2)) * (((-1 : ℤ) ^ (r/2))^3))) := by
  exact HasLead_sub_of_right hA hB hdom

-- Rewrite the left side by `normEDS_odd` with `m = 2*r`.
-- Then normalize exponent and sign:
--   eOdd (r-1) + 3 • eOdd r = eOdd (2*r)
--   - ε_(2r-1) ε_(2r+1)^3 = ε_(4r+1)
```

The other three branches are identical in structure, differing only in which dominance lemma is used and whether the final result is obtained directly (`odd`) or via `HasLead_of_mul_b` (`even`).

### Nonvanishing wrapper

Once `HasLead` is proved, nonvanishing is immediate.

```lean
theorem normEDS_ne_zero_nat_pos (n : ℕ) (hn : 0 < n) :
    W (Int.ofNat n) ≠ 0 := by
  -- Get the relevant odd/even `HasLead` theorem.
  -- Then use `HasLead.ne_zero`.
  sorry

theorem normEDS_ne_zero_int (j : ℤ) (hj : j ≠ 0) :
    W j ≠ 0 := by
  rcases lt_or_gt_of_ne hj with hjneg | hjpos
  · have hpos : W (-j) ≠ 0 := by
      -- `-j` is positive; reduce to `normEDS_ne_zero_nat_pos`.
      sorry
    -- Use the actual oddness theorem for `normEDS`.
    -- `W (-j) = - W j`, or equivalently `W j = - W (-j)`.
    intro hz
    apply hpos
    -- rewrite by oddness and `hz`.
    sorry
  · -- positive integer case
    -- convert `j` to `Int.ofNat j.natAbs` and use `normEDS_ne_zero_nat_pos`.
    sorry
```

## 6. API recommendation

Use this route:

```lean
MvPolynomial.support
MvPolynomial.coeff
MvPolynomial.monomial
MvPolynomial.X
MvPolynomial.coeff_mul      -- or the available coefficient-of-product lemma
MvPolynomial.coeff_add
MvPolynomial.coeff_sub
MvPolynomial.coeff_neg
```

The proof should be driven by a custom predicate like `HasLead`.  This avoids fighting `degrees`/`totalDegree`, which only see the scalar part `(3,8,12)` and therefore cannot distinguish the recurrence summands.

A one-variable `Polynomial.natDegree` route is possible only with an additional bounded encoding of the lex refinement.  For example, for a fixed target bound `N`, choose `M > N^2` and specialize

```lean
b ↦ t^(3*M^3 - M^2),
c ↦ t^(8*M^3 - M),
d ↦ t^(12*M^3 - 1).
```

Then the degree of `b^β c^γ d^δ` is

```text
M^3 wt₀(β,γ,δ) - M^2 β - M γ - δ,
```

which encodes the key `K` for exponent differences bounded by `M`.  But this introduces a bound parameter and extra exponent estimates, so it is more painful in Lean than the direct `MvPolynomial.support` proof.

## 7. Final theorem shape

The final reusable theorem should look like this.

```lean
theorem normEDS_hasLead_pos :
    (∀ r : ℕ, HasLead (W (Int.ofNat (2*r+1)))
        (eOdd r) ((-1 : ℤ) ^ (r / 2))) ∧
    (∀ r : ℕ, 1 ≤ r → HasLead (W (Int.ofNat (2*r)))
        (eEven r) ((-1 : ℤ) ^ ((r - 1) / 2))) := by
  sorry

theorem normEDS_ne_zero_of_ne_zero (j : ℤ) (hj : j ≠ 0) :
    W j ≠ 0 := by
  -- positive case from `normEDS_hasLead_pos`, negative case from `normEDS_neg`.
  sorry
```

This makes Ward's theorem unconditional: every nonzero index has a Ward polynomial with an explicitly exhibited nonzero coefficient, in fact coefficient `±1`, at a uniquely selected monomial.
