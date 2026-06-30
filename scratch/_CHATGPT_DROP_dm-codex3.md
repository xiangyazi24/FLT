# Q2316 Lean drop: QuarticA odd-odd branch via divided Pythagorean triples

This is code-first guidance for the odd-odd branch of `QuarticAParamBridge` in
`FLT/Assumptions/MazurProof/RationalPointsN12.lean`, namespace:

```lean
namespace MazurProof.RationalPointsN12
```

The right Pythagorean object is **not** the original triple

```lean
PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2)
```

but the triple divided by `2`:

```lean
PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2)
```

when `u` and `v` are odd.  The primitive classification of this divided triple should produce `r,s` with

```lean
v ^ 2 = r ^ 2 - s ^ 2
(u ^ 2 + v ^ 2) / 2 = r ^ 2 + s ^ 2
```

hence

```lean
(r + s) * (r - s) = v ^ 2
2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2
```

which are exactly the inputs for `quarticA_eisensteinParam_from_oddLegParams`.

## 1. Parity and divided triple helper lemmas

These are elementary and should be close to sorry-free in the target file.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Odd `u,v` imply `2 ∣ u^2 + v^2`. -/
private theorem quarticA_odd_odd_two_dvd_sum_sq
    {u v : ℤ} (huodd : Odd u) (hvodd : Odd v) :
    (2 : ℤ) ∣ u ^ 2 + v ^ 2 := by
  exact Even.two_dvd ((huodd.pow).add_odd hvodd.pow)

/-- In `PythagoreanTriple Z (2*v^2) H`, if `H` is even, then `Z` is even. -/
private theorem quarticA_two_dvd_left_of_pythagorean_even_hyp
    {Z v H : ℤ}
    (htrip : PythagoreanTriple Z (2 * v ^ 2) H)
    (h2H : (2 : ℤ) ∣ H) :
    (2 : ℤ) ∣ Z := by
  have hHeven : Even H := even_iff_two_dvd.mpr h2H
  have hy_even : Even (2 * v ^ 2) := even_two_mul (v ^ 2)
  have hy_sq_even : Even ((2 * v ^ 2) * (2 * v ^ 2)) :=
    hy_even.mul_right (2 * v ^ 2)
  have hsum_even : Even (Z * Z + (2 * v ^ 2) * (2 * v ^ 2)) := by
    rw [htrip]
    exact hHeven.mul_right H
  have hZ_sq_even : Even (Z * Z) :=
    (Int.even_add.mp hsum_even).mpr hy_sq_even
  have hZeven : Even Z := by
    rcases Int.even_mul.mp hZ_sq_even with hZ | hZ <;> exact hZ
  exact Even.two_dvd hZeven

/--
The correct triple for the odd-odd branch is the original Pythagorean triple divided by `2`.
-/
theorem quarticA_odd_odd_divided_pythagoreanTriple
    {u v Z : ℤ}
    (huodd : Odd u) (hvodd : Odd v)
    (htrip : PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2)) :
    PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2) := by
  have h2H : (2 : ℤ) ∣ u ^ 2 + v ^ 2 :=
    quarticA_odd_odd_two_dvd_sum_sq huodd hvodd
  have h2Z : (2 : ℤ) ∣ Z :=
    quarticA_two_dvd_left_of_pythagorean_even_hyp
      (Z := Z) (v := v) (H := u ^ 2 + v ^ 2) htrip h2H
  apply (PythagoreanTriple.mul_iff
    (x := Z / 2) (y := v ^ 2) (z := (u ^ 2 + v ^ 2) / 2)
    (2 : ℤ) (by norm_num)).mp
  convert htrip using 1
  · rw [mul_comm, Int.ediv_mul_cancel h2Z]
  · ring
  · rw [mul_comm, Int.ediv_mul_cancel h2H]

/-- The divided triple attached directly to `QuarticA`. -/
theorem quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA
    {u v Z : ℤ}
    (huodd : Odd u) (hvodd : Odd v)
    (hA : QuarticA u v Z) :
    PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2) := by
  exact quarticA_odd_odd_divided_pythagoreanTriple
    (u := u) (v := v) (Z := Z) huodd hvodd
    (quarticA_pythagoreanTriple hA)

end MazurProof.RationalPointsN12
```

If `rw [htrip]` in `quarticA_two_dvd_left_of_pythagorean_even_hyp` fails because the reducible definition is not unfolded, replace it by:

```lean
  dsimp [PythagoreanTriple] at htrip
  rw [htrip]
```

or rewrite the whole proof after `dsimp [PythagoreanTriple]`.

## 2. The small exact theorem parameter for the hard primitive-classification substep

The remaining genuinely useful theorem to prove is not Eisenstein-specific.  It is the primitive classification of the divided triple in the odd-odd case, plus the needed coprimality of `(r+s)` and `(r-s)`.

I would package it as the following **theorem parameter** first.  This is not an axiom; it is the exact local theorem that a later proof should supply.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/--
The exact `r,s` data needed from the primitive classification of the divided
Pythagorean triple in the odd-odd branch.

The `Z` argument is kept even though the output does not mention it, because the
proof of this data uses the divided triple with first leg `Z / 2`.
-/
def QuarticAOddOddRSData (u v Z : ℤ) : Prop :=
  ∃ r s : ℤ,
    Int.gcd (r + s) (r - s) = 1 ∧
    v ^ 2 = r ^ 2 - s ^ 2 ∧
    (u ^ 2 + v ^ 2) / 2 = r ^ 2 + s ^ 2

/--
Smallest theorem parameter for the odd-odd branch.
This should be proved from:
* `quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA`,
* primitivity `Int.gcd (Z / 2) (v ^ 2) = 1`,
* Mathlib's `PythagoreanTriple.isPrimitiveClassified_of_coprime`,
* and the oddness of `v ^ 2` to select the branch where `v ^ 2 = r^2 - s^2`.
-/
def QuarticAOddOddRSDataTheorem : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    Odd u →
    Odd v →
    QuarticA u v Z →
    QuarticAOddOddRSData u v Z

end MazurProof.RationalPointsN12
```

This is the clean boundary between elementary wrapper code and the still-nontrivial Pythagorean primitivity/classification proof.

## 3. No-sorry wrapper from `QuarticAOddOddRSData` to `QuarticAEisensteinParam`

Once the `r,s` data above is available, the call to your existing theorem is elementary.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Nonzero square gives nonzero product after rewriting. -/
private theorem add_sub_mul_ne_zero_of_eq_square_of_ne_zero
    {r s v : ℤ}
    (hprod : (r + s) * (r - s) = v ^ 2)
    (hv0 : v ≠ 0) :
    (r + s) * (r - s) ≠ 0 := by
  intro hzero
  have hv_sq_zero : v ^ 2 = 0 := by
    simpa [hzero] using hprod.symm
  have hv_mul_zero : v * v = 0 := by
    simpa [pow_two] using hv_sq_zero
  rcases mul_eq_zero.mp hv_mul_zero with hv | hv
  · exact hv0 hv
  · exact hv0 hv

/--
Convert the `r,s` data from the divided triple into the inputs expected by
`quarticA_eisensteinParam_from_oddLegParams`.
-/
theorem quarticA_eisensteinParam_from_oddOddRSData
    {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (huodd : Odd u) (hvodd : Odd v)
    (hRS : QuarticAOddOddRSData u v Z) :
    QuarticAEisensteinParam u v := by
  rcases hRS with ⟨r, s, hab_coprime, hv_sq, hH⟩
  have hv0 : v ≠ 0 := by
    intro hv
    exact huv0 (by simp [hv])
  have hprod : (r + s) * (r - s) = v ^ 2 := by
    rw [hv_sq]
    ring
  have hab0 : (r + s) * (r - s) ≠ 0 :=
    add_sub_mul_ne_zero_of_eq_square_of_ne_zero hprod hv0
  have h2H : (2 : ℤ) ∣ u ^ 2 + v ^ 2 :=
    quarticA_odd_odd_two_dvd_sum_sq huodd hvodd
  have hhyp : 2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2 := by
    rw [← hH]
    rw [mul_comm, Int.ediv_mul_cancel h2H]
  exact quarticA_eisensteinParam_from_oddLegParams
    (u := u) (v := v) (r := r) (s := s)
    hab0 hab_coprime hprod hhyp

/--
A no-sorry bridge: if the divided-triple `r,s` theorem is provided as a
parameter, the odd-odd `QuarticAParamBridge` branch follows.
-/
theorem QuarticAOddOddParamBridge_of_RSDataTheorem
    (hRSTheorem : QuarticAOddOddRSDataTheorem) :
    QuarticAOddOddParamBridge := by
  intro u v Z hcop huv0 hne huodd hvodd hA
  exact quarticA_eisensteinParam_from_oddOddRSData
    (u := u) (v := v) (Z := Z)
    huv0 huodd hvodd
    (hRSTheorem hcop huv0 hne huodd hvodd hA)

end MazurProof.RationalPointsN12
```

Notice that `u ^ 2 ≠ v ^ 2` is passed through to the `RSData` theorem because the bridge interface includes it, but the final nonzero-product proof above uses `u * v ≠ 0`, specifically `v ≠ 0`.  See the audit note below: `u ^ 2 ≠ v ^ 2` alone is not enough to prove `(r+s)*(r-s) ≠ 0`.

## 4. What the primitive Pythagorean subproof should prove

The divided triple is:

```lean
PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2)
```

The target primitive classification should be staged like this.

```lean
namespace MazurProof.RationalPointsN12

/--
A useful intermediate statement: the divided triple is primitive.
This is the first nontrivial subgoal after division by `2`.
-/
def QuarticAOddOddDividedTriplePrimitiveTheorem : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    Odd u →
    Odd v →
    QuarticA u v Z →
    Int.gcd (Z / 2) (v ^ 2) = 1

/--
A second useful intermediate statement: primitive classification of the divided
triple gives the required `r,s` output.
-/
def QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem : Prop :=
  ∀ {u v Z : ℤ},
    u * v ≠ 0 →
    Odd u →
    Odd v →
    PythagoreanTriple (Z / 2) (v ^ 2) ((u ^ 2 + v ^ 2) / 2) →
    Int.gcd (Z / 2) (v ^ 2) = 1 →
    QuarticAOddOddRSData u v Z

/--
Composition of the two smaller subtheorems gives the exact `RSDataTheorem` above.
-/
theorem QuarticAOddOddRSDataTheorem_of_dividedPrimitive_and_classification
    (hprim : QuarticAOddOddDividedTriplePrimitiveTheorem)
    (hclass : QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem) :
    QuarticAOddOddRSDataTheorem := by
  intro u v Z hcop huv0 hne huodd hvodd hA
  exact hclass huv0 huodd hvodd
    (quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA
      (u := u) (v := v) (Z := Z) huodd hvodd hA)
    (hprim hcop huv0 huodd hvodd hA)

end MazurProof.RationalPointsN12
```

This split is useful because `hprim` is usually the arithmetic gcd argument, while `hclass` is mostly Mathlib Pythagorean classification plus branch selection.

## 5. How to choose `r,s` from Mathlib's primitive classification

Mathlib's classification theorem gives, for a primitive triple:

```lean
PythagoreanTriple.IsPrimitiveClassified
```

whose payload has this shape:

```lean
∃ m n : ℤ,
  (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨
   x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
  Int.gcd m n = 1 ∧
  (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)
```

For the divided triple, use:

```lean
x = Z / 2
y = v ^ 2
z = (u ^ 2 + v ^ 2) / 2
```

Since `v` is odd, `v ^ 2` is odd.  Therefore the branch

```lean
v ^ 2 = 2 * m * n
```

is impossible because the right-hand side is even.  So take

```lean
r = m
s = n
```

from the other branch:

```lean
Z / 2 = 2 * r * s
v ^ 2 = r ^ 2 - s ^ 2
```

Then the triple identity gives, with positive hypotenuse,

```lean
(u ^ 2 + v ^ 2) / 2 = r ^ 2 + s ^ 2
```

A likely extraction skeleton is:

```lean
private theorem odd_square_ne_two_mul
    {v r s : ℤ} (hvodd : Odd v) :
    v ^ 2 ≠ 2 * r * s := by
  intro h
  have hv2odd : Odd (v ^ 2) := hvodd.pow
  have heven_rhs : Even (2 * r * s) := by
    simpa [mul_assoc] using (even_two_mul (r * s) : Even (2 * (r * s)))
  have hv2even : Even (v ^ 2) := by
    simpa [h] using heven_rhs
  exact (Int.not_even_iff_odd.mpr hv2odd) hv2even
```

For the hypotenuse sign, use positivity of

```lean
(u ^ 2 + v ^ 2) / 2
```

which follows from `u * v ≠ 0` and oddness/evenness of the sum.  If the equality of squares is awkward, make it a local helper:

```lean
/-- A helper for the hypotenuse after substituting the classified legs. -/
private theorem pythagorean_hyp_eq_sq_sum_of_second_branch
    {x y H r s : ℤ}
    (htrip : PythagoreanTriple x y H)
    (hHpos : 0 < H)
    (hx : x = 2 * r * s)
    (hy : y = r ^ 2 - s ^ 2) :
    H = r ^ 2 + s ^ 2 := by
  -- Proof route:
  --   1. From `htrip`, `hx`, `hy`, get `H ^ 2 = (r ^ 2 + s ^ 2) ^ 2` by `ring`.
  --   2. Use `sq_eq_sq_iff_eq_or_eq_neg`.
  --   3. Rule out `H = -(r^2+s^2)` using `hHpos` and `sq_nonneg`/`nlinarith`.
  -- This is elementary but slightly theorem-name-sensitive, so keep it separate.
  -- No need to expose this helper outside the proof file.
  have hsq : H ^ 2 = (r ^ 2 + s ^ 2) ^ 2 := by
    rw [← htrip]
    rw [hx, hy]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hsum_nonneg : 0 ≤ r ^ 2 + s ^ 2 := by nlinarith [sq_nonneg r, sq_nonneg s]
    nlinarith
```

If `rw [← htrip]` fails here, first do:

```lean
  dsimp [PythagoreanTriple] at htrip
```

and then run the same `rw`/`ring` proof.

## 6. Coprimality of `(r+s)` and `(r-s)`

The correct extra hypotheses are:

```lean
Int.gcd r s = 1
```

and opposite parity:

```lean
(r % 2 = 0 ∧ s % 2 = 1) ∨ (r % 2 = 1 ∧ s % 2 = 0)
```

These are exactly included in `PythagoreanTriple.IsPrimitiveClassified`.  Under these hypotheses,

```lean
Int.gcd (r + s) (r - s) = 1
```

is true.  The proof route is:

* any common divisor of `r+s` and `r-s` divides `2*r` and `2*s`;
* since `gcd r s = 1`, such a divisor divides `2`;
* because `r` and `s` have opposite parity, both `r+s` and `r-s` are odd, so the common divisor is not even;
* hence the gcd is `1`.

I would add this as a named elementary lemma, or pass it as part of `QuarticAOddOddRSData` until the rest of the branch is stable:

```lean
/-- Elementary lemma to prove later if it is not already in the file. -/
def AddSubCoprimeOfCoprimeOppParityTheorem : Prop :=
  ∀ {r s : ℤ},
    Int.gcd r s = 1 →
    ((r % 2 = 0 ∧ s % 2 = 1) ∨ (r % 2 = 1 ∧ s % 2 = 0)) →
    Int.gcd (r + s) (r - s) = 1
```

This is not a hard arithmetic theorem, but it is a good isolated Lean chore.  Keeping it isolated avoids polluting the main QuarticA branch with gcd/divisibility bookkeeping.

## 7. Nonzero product audit

The hypothesis

```lean
u ^ 2 ≠ v ^ 2
```

**does not by itself** imply

```lean
(r + s) * (r - s) ≠ 0
```

from the equations

```lean
(r + s) * (r - s) = v ^ 2
2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2
```

Indeed, `(r+s)*(r-s)=0` only gives `v=0`; it does not force `u^2=v^2`.  For example, algebraically one can have `v=0` and `u≠0`.  In the actual bridge, use

```lean
u * v ≠ 0
```

to get `v ≠ 0`, and then use `hprod : (r+s)*(r-s)=v^2` to prove `hab0`.  The helper

```lean
add_sub_mul_ne_zero_of_eq_square_of_ne_zero
```

above does exactly this.

## 8. Recommended next implementation order

1. Add and test the elementary divided-triple lemmas:

```lean
quarticA_odd_odd_two_dvd_sum_sq
quarticA_two_dvd_left_of_pythagorean_even_hyp
quarticA_odd_odd_divided_pythagoreanTriple
quarticA_odd_odd_divided_pythagoreanTriple_of_quarticA
```

2. Add the no-sorry wrapper:

```lean
QuarticAOddOddParamBridge_of_RSDataTheorem
```

3. Prove the small theorem parameter in two parts:

```lean
QuarticAOddOddDividedTriplePrimitiveTheorem
QuarticAOddOddRSDataOfPrimitiveDividedTripleTheorem
```

4. Only then inline or replace `QuarticAOddOddRSDataTheorem` by the composed proof.

This keeps the branch auditable: the only real missing work is the primitive divided-triple proof and the standard extraction of the correct Pythagorean branch.