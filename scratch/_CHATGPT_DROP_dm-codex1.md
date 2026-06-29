# Q2288: QuarticA audit for `RationalPointsN12.lean`

Target file: `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.

This drop is specifically about **QuarticA**, not QuarticB.

We are auditing

```lean
Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)
```

under `Int.gcd u v = 1` and `u * v ≠ 0`.

## Executive conclusion

`QuarticA` is **not** the same residual as the existing `pythagoreanQuarticRhs` / NonAxisSignedResidual path used for the B-channel.  The B-channel twist produces a quartic of the shape

```lean
m ^ 4 + 8 * m ^ 3 * n + 2 * m ^ 2 * n ^ 2 - 8 * m * n ^ 3 + n ^ 4
```

whereas `QuarticA` naturally reduces to the classical Ljunggren/Eisenstein quartic

```lean
c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4
```

So the clean Lean split is:

1. prove elementary bridge lemmas from `QuarticA` to a primitive Pythagorean triple with one square leg;
2. parametrize that triple using `PythagoreanTriple.coprime_classification`;
3. reduce to one new residual theorem, stated as a Ljunggren quartic residual.

The final theorem should state that primitive nonzero `QuarticA` has only the trivial branch `u ^ 2 = v ^ 2`.

## 1. Correct theorem statement for `quartic_A_only_trivial`

Use this as the curve-facing theorem:

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Data.Int.Parity
import Mathlib.Tactic

/-- Optional local abbreviation.  Do not introduce this if the file already has
its own naming convention for residual A. -/
def QuarticA (u v Z : ℤ) : Prop :=
  Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)

/-- Primitive nonzero QuarticA has only the degenerate square branch. -/
theorem quartic_A_only_trivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    u ^ 2 = v ^ 2 := by
  by_contra hneq
  obtain ⟨m, n, hmn0, hmncop, hv_mn, hu_lj⟩ :=
    quartic_A_nontrivial_to_ljunggren_parameters
      hcop huv0 hneq hA
  exact hneq
    (quartic_A_finish_from_ljunggren_parameters
      hmn0 hmncop hv_mn hu_lj)
```

The theorem above assumes these two supporting interfaces exist:

```lean
/-- Elementary bridge, to be proved from Pythagorean triples and coprime square-factor splitting.
This is not a new number-theory residual. -/
-- theorem quartic_A_nontrivial_to_ljunggren_parameters
--     {u v Z : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (huv0 : u * v ≠ 0)
--     (hneq : u ^ 2 ≠ v ^ 2)
--     (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
--     ∃ m n : ℤ,
--       m * n ≠ 0 ∧
--       Int.gcd m n = 1 ∧
--       v ^ 2 = (m * n) ^ 2 ∧
--       u ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4

/-- RESIDUAL A / Ljunggren quartic.  This is the genuinely new classical residual. -/
axiom ljunggren_quartic_square_eq_mul_square
    {m n c : ℤ}
    (hcop : Int.gcd m n = 1)
    (hmn0 : m * n ≠ 0)
    (h : c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) :
    c ^ 2 = (m * n) ^ 2

/-- Pure wiring: consume the Ljunggren residual after the elementary bridge has produced parameters. -/
theorem quartic_A_finish_from_ljunggren_parameters
    {u v m n : ℤ}
    (hmn0 : m * n ≠ 0)
    (hcop : Int.gcd m n = 1)
    (hv : v ^ 2 = (m * n) ^ 2)
    (hu : u ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) :
    u ^ 2 = v ^ 2 := by
  have hu' : u ^ 2 = (m * n) ^ 2 :=
    ljunggren_quartic_square_eq_mul_square hcop hmn0 hu
  exact hu'.trans hv.symm
```

There is also a useful contradiction wrapper:

```lean
theorem quartic_A_no_nontrivial
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2))
    (hneq : u ^ 2 ≠ v ^ 2) :
    False := by
  exact hneq (quartic_A_only_trivial hcop huv0 hA)
```

If you want the full trivial classification, add it separately.  From `hcop`, `huv0`, and `u ^ 2 = v ^ 2`, one can additionally derive `u ^ 2 = 1`, `v ^ 2 = 1`, and `Z = 0`.  The boundary proof usually only needs `u ^ 2 = v ^ 2`.

## 2. Route from A to a new residual

The key identity is elementary:

```lean
lemma quartic_A_to_pythagorean_identity
    {u v Z : ℤ}
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  rw [hA]
  ring
```

So `QuarticA` gives a Pythagorean triple

```lean
Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2
```

or, if `u` and `v` are both odd, after dividing the common factor `2`, a primitive triple

```lean
W ^ 2 + (v ^ 2) ^ 2 = H ^ 2
```

where `Z = 2 * W` and `u ^ 2 + v ^ 2 = 2 * H`.

The elementary bridge should prove this exact parametrization theorem:

```lean
/-- Elementary QuarticA-to-Ljunggren bridge.

Proof ingredients:
* `quartic_A_to_pythagorean_identity`;
* `Int.gcd Z v = 1` from `Int.gcd u v = 1` and `hA`;
* parity split: `Odd (u + v)` versus `Odd u ∧ Odd v`;
* `PythagoreanTriple.coprime_classification`;
* coprime product of a square implies both factors are squares.
-/
-- theorem quartic_A_nontrivial_to_ljunggren_parameters
--     {u v Z : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (huv0 : u * v ≠ 0)
--     (hneq : u ^ 2 ≠ v ^ 2)
--     (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
--     ∃ m n : ℤ,
--       m * n ≠ 0 ∧
--       Int.gcd m n = 1 ∧
--       v ^ 2 = (m * n) ^ 2 ∧
--       u ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4
```

Then the only hard residual left is exactly:

```lean
/-- RESIDUAL A / Ljunggren.
Equivalent classical statement: if `gcd m n = 1`, `m n ≠ 0`, and
`m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4` is a square, then the square is the
trivial one.  Since `gcd m n = 1`, this forces `m ^ 2 = n ^ 2 = 1`,
hence `c ^ 2 = (m * n) ^ 2`.
-/
axiom ljunggren_quartic_square_eq_mul_square
    {m n c : ℤ}
    (hcop : Int.gcd m n = 1)
    (hmn0 : m * n ≠ 0)
    (h : c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4) :
    c ^ 2 = (m * n) ^ 2
```

This is an Eisenstein-integer / FLT3-style residual: the expression is

```text
Norm(m^2 + n^2 * ω) = m^4 - m^2 n^2 + n^4
```

for an Eisenstein unit `ω` satisfying `ω^2 + ω + 1 = 0`.  It is not the B-channel quartic.

## 3. Mathlib/API patterns to use

The current file already checked the Pythagorean-triple route for B via Mathlib.  For A, use the same API but with a different final quartic.

Search/check these names:

```text
#check PythagoreanTriple.coprime_classification
#check PythagoreanTriple.classification
grep -R "coprime_classification" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
grep -R "PythagoreanTriple" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
```

Expected usable shape, up to field order and names:

```lean
-- Expected shape, not necessarily exact binder order:
-- PythagoreanTriple.coprime_classification
--   (hpy : x ^ 2 + y ^ 2 = z ^ 2)
--   (hcop : Int.gcd x y = 1)
--   : ∃ a b : ℤ,
--       Int.gcd a b = 1 ∧
--       Odd (a + b) ∧
--       ((x = a ^ 2 - b ^ 2 ∧ y = 2 * a * b) ∨
--        (x = 2 * a * b ∧ y = a ^ 2 - b ^ 2)) ∧
--       z = a ^ 2 + b ^ 2
```

If the theorem is phrased with a structure/proposition rather than a raw equation, first build the structure from the equation using the constructor in the same namespace.  The earlier B proof in this file should show the exact constructor pattern.

For square-factor splitting, either use an existing Mathlib theorem if present, or prove this generic local helper once using `Nat.factorization`:

```lean
-- Generic helper statement to prove locally; it is not curve-specific.
-- theorem Int.exists_sq_factors_of_coprime_mul_sq
--     {a b c : ℤ}
--     (ha : 0 ≤ a)
--     (hb : 0 ≤ b)
--     (hcop : Int.gcd a b = 1)
--     (hmul : a * b = c ^ 2) :
--     ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2
```

A Nat version is often easier:

```lean
-- theorem Nat.exists_sq_factors_of_coprime_mul_sq
--     {a b c : ℕ}
--     (hcop : Nat.Coprime a b)
--     (hmul : a * b = c ^ 2) :
--     ∃ r s : ℕ, a = r ^ 2 ∧ b = s ^ 2
```

Then lift back to `ℤ` with `Int.natAbs`.  This is standard unique-factorization bookkeeping, not a new residual.

## 4. Paste-oriented algebra lemmas

These are local ring/positivity lemmas worth adding before the hard residual.

```lean
lemma quartic_A_to_pythagorean_identity
    {u v Z : ℤ}
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2 := by
  rw [hA]
  ring

lemma quartic_A_second_factor_pos
    {u v : ℤ}
    (hv0 : v ≠ 0) :
    0 < u ^ 2 + 3 * v ^ 2 := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_ne_zero v hv0
  nlinarith

lemma quartic_A_first_factor_nonneg
    {u v Z : ℤ}
    (hv0 : v ≠ 0)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    0 ≤ u ^ 2 - v ^ 2 := by
  have hsec : 0 < u ^ 2 + 3 * v ^ 2 :=
    quartic_A_second_factor_pos (u := u) hv0
  have hprod : 0 ≤ (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) := by
    rw [← hA]
    exact sq_nonneg Z
  exact nonneg_of_mul_nonneg_right hprod hsec

lemma quartic_A_first_factor_pos_of_nontrivial
    {u v Z : ℤ}
    (hv0 : v ≠ 0)
    (hneq : u ^ 2 ≠ v ^ 2)
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
    0 < u ^ 2 - v ^ 2 := by
  have hnonneg : 0 ≤ u ^ 2 - v ^ 2 :=
    quartic_A_first_factor_nonneg (u := u) (v := v) (Z := Z) hv0 hA
  have hne : u ^ 2 - v ^ 2 ≠ 0 := by
    intro hzero
    exact hneq (sub_eq_zero.mp hzero)
  exact lt_of_le_of_ne hnonneg hne.symm

lemma quartic_A_Z_eq_zero_of_trivial
    {u v Z : ℤ}
    (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2))
    (htriv : u ^ 2 = v ^ 2) :
    Z = 0 := by
  have hZsq : Z ^ 2 = 0 := by
    rw [hA, htriv]
    ring
  exact sq_eq_zero_iff.mp hZsq
```

If `sq_pos_of_ne_zero` or `sq_eq_zero_iff` has a slightly different namespace in the local Mathlib version, `grep` for those exact names; the proofs above are otherwise just ordered-ring facts plus `ring`.

### GCD and parity helper statements

Add these as elementary helper targets.  The proofs are by prime divisors and parity cases; no curve theory is involved.

```lean
-- theorem quartic_A_coprime_Z_v
--     {u v Z : ℤ}
--     (hcop : Int.gcd u v = 1)
--     (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2)) :
--     Int.gcd Z v = 1

-- theorem quartic_A_not_both_even
--     {u v : ℤ}
--     (hcop : Int.gcd u v = 1) :
--     ¬ (Even u ∧ Even v)
```

Proof idea for `quartic_A_coprime_Z_v`: if a prime `p` divides both `Z` and `v`, then reducing `hA` modulo `p` gives `0 = u ^ 4`, hence `p ∣ u`, contradicting `Int.gcd u v = 1`.

Lean-friendly prime-divisor sublemma shape:

```lean
-- lemma quartic_A_no_prime_divides_Z_and_v
--     {u v Z : ℤ} {p : ℕ}
--     (hp : Nat.Prime p)
--     (hcop : Int.gcd u v = 1)
--     (hA : Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2))
--     (hpZ : (p : ℤ) ∣ Z)
--     (hpv : (p : ℤ) ∣ v) :
--     False
```

For parity, do not add a parity hypothesis to `quartic_A_only_trivial`.  Split internally:

```lean
-- by_cases hpar : Odd (u + v)
-- · -- opposite-parity branch: primitive triple
-- · -- with `Int.gcd u v = 1`, not opposite parity means `Odd u ∧ Odd v`;
--   -- divide the Pythagorean triple by the common factor 2.
```

`Odd (u + v)` is the correct Lean-friendly test for `u` and `v` having opposite parity, once `Int.gcd u v = 1` has ruled out the both-even case.  If `¬ Odd (u + v)`, then `u` and `v` have the same parity; with coprime integers, that means both are odd.

## 5. Ring identities for the two parametrization branches

### Opposite-parity branch

When `Odd (u + v)`, the triple

```lean
Z ^ 2 + (2 * v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2
```

is primitive.  Classification gives parameters `A B` with the even leg equal to `2 * A * B`.  Because the even leg is `2 * v ^ 2`, we get

```lean
v ^ 2 = A * B
u ^ 2 + v ^ 2 = A ^ 2 + B ^ 2
```

and coprime square-factor splitting gives `A = m ^ 2`, `B = n ^ 2` after harmless sign normalization.  Then use:

```lean
lemma quartic_A_even_leg_sum_identity
    {A B m n : ℤ}
    (hA : A = m ^ 2)
    (hB : B = n ^ 2) :
    A ^ 2 + B ^ 2 = m ^ 4 + n ^ 4 := by
  rw [hA, hB]
  ring

lemma quartic_A_even_leg_product_identity
    {A B m n : ℤ}
    (hA : A = m ^ 2)
    (hB : B = n ^ 2) :
    A * B = (m * n) ^ 2 := by
  rw [hA, hB]
  ring
```

Finally:

```lean
lemma quartic_A_ljunggren_from_sum_and_product
    {u v m n : ℤ}
    (hH : u ^ 2 + v ^ 2 = m ^ 4 + n ^ 4)
    (hv : v ^ 2 = (m * n) ^ 2) :
    u ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  calc
    u ^ 2 = (u ^ 2 + v ^ 2) - v ^ 2 := by ring
    _ = (m ^ 4 + n ^ 4) - (m * n) ^ 2 := by rw [hH, hv]
    _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by ring
```

### Odd-odd branch

When `u` and `v` are both odd, the raw triple has common factor `2`.  Write

```lean
Z = 2 * W
u ^ 2 + v ^ 2 = 2 * H
```

and get the primitive triple

```lean
W ^ 2 + (v ^ 2) ^ 2 = H ^ 2
```

where `v ^ 2` is the odd leg.  Classification gives

```lean
v ^ 2 = A ^ 2 - B ^ 2 = (A - B) * (A + B)
H = A ^ 2 + B ^ 2
```

with `A - B` and `A + B` coprime positive odd factors.  Square-factor splitting gives

```lean
A - B = m ^ 2
A + B = n ^ 2
```

The needed ring identities are:

```lean
lemma quartic_A_odd_branch_product_identity
    {A B m n : ℤ}
    (hm : A - B = m ^ 2)
    (hn : A + B = n ^ 2) :
    A ^ 2 - B ^ 2 = (m * n) ^ 2 := by
  calc
    A ^ 2 - B ^ 2 = (A - B) * (A + B) := by ring
    _ = m ^ 2 * n ^ 2 := by rw [hm, hn]
    _ = (m * n) ^ 2 := by ring

lemma quartic_A_odd_branch_sum_identity
    {A B m n : ℤ}
    (hm : A - B = m ^ 2)
    (hn : A + B = n ^ 2) :
    2 * (A ^ 2 + B ^ 2) = m ^ 4 + n ^ 4 := by
  calc
    2 * (A ^ 2 + B ^ 2) = (A - B) ^ 2 + (A + B) ^ 2 := by ring
    _ = (m ^ 2) ^ 2 + (n ^ 2) ^ 2 := by rw [hm, hn]
    _ = m ^ 4 + n ^ 4 := by ring
```

Combining `u ^ 2 + v ^ 2 = 2 * H`, `H = A ^ 2 + B ^ 2`, and `v ^ 2 = A ^ 2 - B ^ 2` with the two lemmas above again gives

```lean
v ^ 2 = (m * n) ^ 2
u ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4
```

## 6. False shortcuts and sanity checks

* `QuarticA` does **not** become the existing `pythagoreanQuarticRhs` residual after the first Pythagorean parametrization.  It becomes `m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4`.

* It is false that `u ^ 2 - v ^ 2` is forced to be zero by a simple sign argument.  The second factor `u ^ 2 + 3 * v ^ 2` is positive, and `hA` only gives `0 ≤ u ^ 2 - v ^ 2`.  Nontrivial positive cases are eliminated by the Ljunggren residual, not by positivity.

* The final statement `u ^ 2 = v ^ 2` is true under `Int.gcd u v = 1` and `u * v ≠ 0`.  The actual primitive affine possibilities in this residual are the degenerate ones `u = ±1`, `v = ±1`, `Z = 0`.

* The hypothesis `u * v ≠ 0` is necessary.  If `v = 0`, then `hA` becomes `Z ^ 2 = u ^ 4`, giving many nontrivial solutions and not `u ^ 2 = v ^ 2`.

* Small nontrivial checks line up with the residual: `(u, v) = (2, 1)` gives `21`, `(3, 1)` gives `96`, `(3, 2)` gives `105`, and `(5, 1)` gives `672`, none squares.  The only primitive nonzero solutions are the zero-product branch of the first factor, i.e. `u ^ 2 = v ^ 2`.

## 7. Recommended implementation order

1. Add the ring lemmas in section 4 and the branch ring identities in section 5.
2. Add the generic square-factor helper for coprime products.
3. Prove `quartic_A_coprime_Z_v` and the parity split helpers.
4. Prove `quartic_A_nontrivial_to_ljunggren_parameters` using `PythagoreanTriple.coprime_classification` in the two parity branches.
5. Add the single hard residual interface `ljunggren_quartic_square_eq_mul_square` and prove it separately via Eisenstein/FLT3/Ljunggren descent.
6. Finish `quartic_A_only_trivial` with the short wrapper above.
