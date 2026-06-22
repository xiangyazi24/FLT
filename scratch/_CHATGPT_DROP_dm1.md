# Q303-dm1: universal `normEDS` nonvanishing in `ℤ[b,c,d]`

## Executive answer

Yes.  In the universal ring

```lean
U := MvPolynomial (Fin 3) ℤ
bU := MvPolynomial.X 0
cU := MvPolynomial.X 1
dU := MvPolynomial.X 2
W  := normEDS bU cU dU
```

one has

```lean
∀ j : ℤ, j ≠ 0 → normEDS bU cU dU j ≠ 0.
```

The cleanest proof is **specialization**, but not to a non-torsion elliptic curve.  Use the degenerate EDS specialization

```text
(b,c,d) = (2,3,2).
```

For these parameters,

```text
normEDS 2 3 2 j = j
```

for every integer `j`.  Therefore, if the universal polynomial `normEDS bU cU dU j` were zero, evaluating at `(2,3,2)` would give `j = 0`, contradiction.

This is much easier than primitive divisors, leading terms, or division polynomials.

---

## Why `(2,3,2)` works

The identity sequence

```text
I(j) := j
```

has the normalized initial values

```text
I(0)=0,
I(1)=1,
I(2)=2,
I(3)=3,
I(4)=4=2·2.
```

So it matches `normEDS b c d` with

```text
b = 2,
c = 3,
d = 2.
```

It also satisfies the EDS defining recurrences.

Adjacent Somos becomes

```text
(m+2)(m-2) = 2^2 (m+1)(m-1) - 3m^2.
```

Indeed both sides are `m^2 - 4`:

```text
(m+2)(m-2) = m^2 - 4,
4(m+1)(m-1) - 3m^2 = 4(m^2-1)-3m^2 = m^2-4.
```

The standard normalized odd recurrence becomes

```text
I(2n+1)
= I(n+2) I(n)^3 - I(n-1) I(n+1)^3.
```

The polynomial check is

```text
(n+2)n^3 - (n-1)(n+1)^3 = 2n+1.
```

The standard normalized even recurrence, in the division-free form, is

```text
2 · I(2n)
= I(n) · ( I(n+2) I(n-1)^2 - I(n-2) I(n+1)^2 ).
```

The polynomial check is

```text
n · ((n+2)(n-1)^2 - (n-2)(n+1)^2) = 4n = 2 · (2n).
```

Since `2 ≠ 0` in `ℤ`, cancellation gives `I(2n)=2n`.

Negative indices match because both `normEDS` and `I` are odd:

```text
normEDS b c d (-j) = - normEDS b c d j,
I(-j) = -I(j).
```

---

## Main Lean lemma chain

### 1. Prove the concrete specialization

This is the key lemma:

```lean
lemma normEDS_232_eq_id (j : ℤ) :
    normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) j = j := by
  -- prove first for nonnegative natural indices by strong induction,
  -- then extend to negative integers using `normEDS_neg`.
  sorry
```

A good formal split is:

```lean
lemma normEDS_232_nat (n : ℕ) :
    normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) (n : ℤ) = (n : ℤ) := by
  classical
  refine Nat.strong_induction_on n ?_
  intro n ih
  -- Cases n = 0,1,2,3,4 are `simp [normEDS]` or the existing base lemmas.
  -- For n ≥ 5, split by parity.
  -- Odd case: n = 2*q+1, q ≥ 2.
  -- Even case: n = 2*q, q ≥ 3.
  sorry

lemma normEDS_232_eq_id (j : ℤ) :
    normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) j = j := by
  -- case split j as a natural integer or a negative successor
  -- use `normEDS_232_nat` on the positive part
  -- use the already-proved oddness theorem for `normEDS`
  sorry
```

The two recurrence subgoals after rewriting by the induction hypotheses are just:

```lean
example (n : ℤ) :
    (n + 2) * n^3 - (n - 1) * (n + 1)^3 = 2*n + 1 := by
  ring

example (n : ℤ) :
    n * ((n + 2) * (n - 1)^2 - (n - 2) * (n + 1)^2) = 4*n := by
  ring
```

If your even recurrence is stated in multiplied form, the even branch should look like this schematically:

```lean
-- goal: normEDS 2 3 2 (2*q : ℤ) = (2*q : ℤ)
have hmul :
    (2 : ℤ) * normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) ((2*q : ℕ) : ℤ)
      = (2 : ℤ) * ((2*q : ℕ) : ℤ) := by
  -- rewrite by `normEDS_even`, use IH on q-2,q-1,q,q+1,q+2,
  -- then close by the polynomial identity above.
  ring_nf
exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hmul
```

The only arithmetic side conditions needed by the strong induction are:

```text
q ≥ 2  ⇒  q-1 < 2q+1, q < 2q+1, q+1 < 2q+1, q+2 < 2q+1,
q ≥ 3  ⇒  q-2 < 2q, q-1 < 2q, q < 2q, q+1 < 2q, q+2 < 2q.
```

In Lean, dispatch these with `omega`.

Recommended helper lemmas:

```lean
lemma odd_poly_232 (n : ℤ) :
    (n + 2) * n^3 - (n - 1) * (n + 1)^3 = 2*n + 1 := by
  ring

lemma even_poly_232 (n : ℤ) :
    n * ((n + 2) * (n - 1)^2 - (n - 2) * (n + 1)^2) = 4*n := by
  ring
```

Then the recurrence branches are just `rw`/`simp`/`ring_nf` after applying IH.

---

### 2. Universal nonvanishing by evaluation

Use the evaluation homomorphism

```lean
φ : MvPolynomial (Fin 3) ℤ →+* ℤ
φ := MvPolynomial.aeval (![2, 3, 2] : Fin 3 → ℤ)
```

The universal nonvanishing lemma is:

```lean
abbrev EDSU := MvPolynomial (Fin 3) ℤ

abbrev bU : EDSU := MvPolynomial.X 0
abbrev cU : EDSU := MvPolynomial.X 1
abbrev dU : EDSU := MvPolynomial.X 2

lemma universal_normEDS_ne_zero {j : ℤ} (hj : j ≠ 0) :
    normEDS bU cU dU j ≠ 0 := by
  intro hzero
  let φ : EDSU →+* ℤ := MvPolynomial.aeval (![2, 3, 2] : Fin 3 → ℤ)
  have hmap := congrArg φ hzero
  have hz : normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) j = 0 := by
    -- `map_normEDS` rewrites evaluation of universal normEDS.
    -- `simp [φ, bU, cU, dU, map_normEDS]` should reduce the variables.
    simpa [φ, bU, cU, dU, map_normEDS] using hmap
  have hj0 : j = 0 := by
    simpa [normEDS_232_eq_id] using hz
  exact hj hj0
```

Depending on the exact statement of `map_normEDS` in your repo, the middle block may need to be oriented as one of these:

```lean
have hmapEDS :
    φ (normEDS bU cU dU j)
      = normEDS (φ bU) (φ cU) (φ dU) j := by
  simpa using map_normEDS φ bU cU dU j
```

or

```lean
rw [map_normEDS] at hmap
simp [φ, bU, cU, dU] at hmap
```

The mathematical content is simply:

```text
0 = φ(0)
  = φ(normEDS bU cU dU j)
  = normEDS 2 3 2 j
  = j,
```

contradicting `j ≠ 0`.

---

### 3. Remove the domain/nonvanishing hypothesis globally

Now apply your conditional Ward theorem only in the universal domain.

```lean
lemma universal_isEllSequence :
    IsEllSequence (normEDS bU cU dU) := by
  exact ward_conditional_domain_nonzero
    (R := EDSU)
    (b := bU) (c := cU) (d := dU)
    (hne := by
      intro j hj
      exact universal_normEDS_ne_zero hj)
```

Here `EDSU` is an integral domain because `ℤ` is an integral domain and multivariate polynomial rings over a domain are domains.  This should be found by typeclass search:

```lean
example : IsDomain EDSU := inferInstance
```

Then transport to an arbitrary commutative ring:

```lean
lemma isEllSequence_map
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {W : ℤ → R}
    (hW : IsEllSequence W) :
    IsEllSequence (fun n => φ (W n)) := by
  intro m n r
  -- `IsEllSequence` is a polynomial identity, so apply `φ` to `hW m n r`.
  simpa using congrArg φ (hW m n r)
```

Finally:

```lean
theorem normEDS_isEllSequence_unconditional
    {R : Type*} [CommRing R] (b c d : R) :
    IsEllSequence (normEDS b c d) := by
  let φ : EDSU →+* R := MvPolynomial.aeval (![b, c, d] : Fin 3 → R)
  have hmap := isEllSequence_map φ universal_isEllSequence
  intro m n r
  specialize hmap m n r
  -- rewrite every `φ (normEDS bU cU dU _)` to `normEDS b c d _`.
  simpa [φ, bU, cU, dU, map_normEDS] using hmap
```

This is the standard universal-polynomial-identity transport pattern.  The target ring `R` need not be a domain and no nonvanishing is needed after transport.

---

## Assessment of the three proposed strategies

### (a) Specialization

Best, with the specialization

```text
(b,c,d) = (2,3,2),   normEDS 2 3 2 j = j.
```

This is better than using a non-torsion elliptic curve.  A non-torsion elliptic curve proof would require importing or reproving the link between zero EDS terms and torsion, plus a proof that the chosen point has infinite order.  The degenerate identity sequence avoids all of that.

Lean tractability: **very high**.  The proof is just strong induction, the two normEDS recurrences, `ring`, `omega`, and evaluation by `MvPolynomial.aeval`.

### (b) Degree / leading term

Valid in principle but unnecessarily expensive.  A naive leading monomial argument has real cancellation traps.  For example, with lexicographic or weighted orders, the top-degree parts of the two recurrence products can tie and partially cancel at small indices such as the `W(7)` / `W(11)` pattern.  You would need a stronger invariant describing the actual leading coefficient, not just the leading degree.

Lean tractability: **medium to low**.  It is doable, but it creates a second tropical/monomial-order proof unrelated to the Ward theorem.

### (c) Division polynomials

Not the clean route.  Even if Mathlib has nonzero/natDegree lemmas for division polynomials such as a `natDegree_preΨ`-style theorem, that only says the universal division polynomial is nonzero as a polynomial.  It does not immediately imply that its specialization/evaluation at the universal Ward point `(b,c,d)` is nonzero.  You would still need to formalize the full identification between `normEDS b c d n` and the evaluated division polynomial under the Ward parameterization of the curve and point.  That identification is substantially heavier than the specialization proof above.

Lean tractability: **low** for this task.  It is conceptually elegant but overkill.

---

## Final recommended lemma stack

Implement these in this order:

```lean
lemma odd_poly_232 (n : ℤ) :
    (n + 2) * n^3 - (n - 1) * (n + 1)^3 = 2*n + 1 := by
  ring

lemma even_poly_232 (n : ℤ) :
    n * ((n + 2) * (n - 1)^2 - (n - 2) * (n + 1)^2) = 4*n := by
  ring

lemma normEDS_232_nat (n : ℕ) :
    normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) (n : ℤ) = (n : ℤ) := by
  -- strong induction using `normEDS_odd`, `normEDS_even`, `odd_poly_232`, `even_poly_232`
  sorry

lemma normEDS_232_eq_id (j : ℤ) :
    normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) j = j := by
  -- reduce to `normEDS_232_nat`; negative case by oddness of `normEDS`
  sorry

lemma universal_normEDS_ne_zero {j : ℤ} (hj : j ≠ 0) :
    normEDS bU cU dU j ≠ 0 := by
  intro hzero
  let φ : EDSU →+* ℤ := MvPolynomial.aeval (![2, 3, 2] : Fin 3 → ℤ)
  have hmap := congrArg φ hzero
  have hz : normEDS (2 : ℤ) (3 : ℤ) (2 : ℤ) j = 0 := by
    simpa [φ, bU, cU, dU, map_normEDS] using hmap
  exact hj (by simpa [normEDS_232_eq_id] using hz)

lemma universal_isEllSequence :
    IsEllSequence (normEDS bU cU dU) := by
  exact ward_conditional_domain_nonzero
    (R := EDSU)
    (b := bU) (c := cU) (d := dU)
    (hne := by intro j hj; exact universal_normEDS_ne_zero hj)

theorem normEDS_isEllSequence_unconditional
    {R : Type*} [CommRing R] (b c d : R) :
    IsEllSequence (normEDS b c d) := by
  let φ : EDSU →+* R := MvPolynomial.aeval (![b, c, d] : Fin 3 → R)
  have hmap := isEllSequence_map φ universal_isEllSequence
  intro m n r
  specialize hmap m n r
  simpa [φ, bU, cU, dU, map_normEDS] using hmap
```

The only nontrivial new proof is `normEDS_232_eq_id`; it is elementary arithmetic.  Once that is in place, universal nonvanishing and unconditional Ward are immediate.
