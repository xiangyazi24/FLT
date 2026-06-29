# Q2278: Lean bridge for the N=12 Pythagorean twist

This note is for `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, around the existing definition

```lean
def pythagoreanQuarticRhs (m n : ℤ) : ℤ :=
  m ^ 4 + 8 * m ^ 3 * n + 2 * m ^ 2 * n ^ 2 - 8 * m * n ^ 3 + n ^ 4
```

The requested theorem should not need a new descent argument. It is a wrapper around Mathlib's primitive integer Pythagorean triple classification plus two `ring` identities.

The important point is that Mathlib's primitive theorem already handles arbitrary signs of the two legs and both leg orientations. So for the main theorem below, do **not** introduce a custom eight-sign Pythagorean parametrization unless the existing local file already has one that is easier to consume.

---

## 1. Mathlib theorem names/API to grep

Import:

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic
```

Search patterns in a local checkout:

```bash
grep -R "def PythagoreanTriple" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
grep -R "coprime_classification" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
grep -R "even_odd_of_coprime" .lake/packages/mathlib/Mathlib/NumberTheory/PythagoreanTriples.lean
```

Lean checks that should work on current Mathlib:

```lean
#check PythagoreanTriple
#check PythagoreanTriple.eq
#check PythagoreanTriple.symm
#check PythagoreanTriple.even_odd_of_coprime
#check PythagoreanTriple.coprime_classification
#check PythagoreanTriple.coprime_classification'
#check PythagoreanTriple.classification
```

Expected statement shapes:

```lean
-- def PythagoreanTriple (x y z : ℤ) : Prop :=
--   x * x + y * y = z * z

-- Primitive classification, signed and with the two legs allowed to swap.
#check PythagoreanTriple.coprime_classification
-- PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔
--   ∃ m n : ℤ,
--     (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨
--      x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
--     (z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)) ∧
--     Int.gcd m n = 1 ∧
--     (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)

-- More oriented version, useful only if you know which leg is odd and `0 < z`.
#check PythagoreanTriple.coprime_classification'
-- (h : PythagoreanTriple x y z) ->
-- Int.gcd x y = 1 -> x % 2 = 1 -> 0 < z ->
--   ∃ m n : ℤ,
--     x = m ^ 2 - n ^ 2 ∧
--     y = 2 * m * n ∧
--     z = m ^ 2 + n ^ 2 ∧
--     Int.gcd m n = 1 ∧
--     (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧
--     0 ≤ m
```

For this bridge, prefer `PythagoreanTriple.coprime_classification`, not the primed theorem, because the theorem you want has no positivity hypothesis on `s` and does not specify which of `R,S` is the odd leg.

---

## 2. Parity hypothesis: is `Odd (R + S)` right?

Mathematically, yes: for a primitive Pythagorean triple, exactly one leg is even and the other is odd, so `R + S` is odd. In Lean, however, the hypothesis

```lean
(hpar : Odd (R + S))
```

is redundant for this proof. `PythagoreanTriple.coprime_classification` derives opposite parity of the parameters `m,n` from `hs` and `hcop`.

If a local older lemma requires opposite parity of `R,S`, use Mathlib's theorem instead of destructing `hpar`:

```lean
have hpy : PythagoreanTriple R S s := by
  dsimp [PythagoreanTriple]
  calc
    R * R + S * S = R ^ 2 + S ^ 2 := by ring
    _ = s ^ 2 := hs.symm
    _ = s * s := by ring

have hRS_parity :
    R % 2 = 0 ∧ S % 2 = 1 ∨ R % 2 = 1 ∧ S % 2 = 0 :=
  hpy.even_odd_of_coprime hcop
```

For the final requested conclusion, convert Mathlib's parameter parity to `Odd (m + n)`. The following helper is the robust pattern. If `rw [Int.odd_iff]` does not fire in your pinned Mathlib, grep for `odd_iff` and replace that one line with the local theorem name; the surrounding proof is unchanged.

```lean
private lemma odd_add_of_emod_zero_one {a b : ℤ}
    (ha : a % 2 = 0) (hb : b % 2 = 1) : Odd (a + b) := by
  rw [Int.odd_iff]
  rw [Int.add_emod, ha, hb]
  norm_num

private lemma odd_add_of_emod_one_zero {a b : ℤ}
    (ha : a % 2 = 1) (hb : b % 2 = 0) : Odd (a + b) := by
  rw [add_comm]
  exact odd_add_of_emod_zero_one hb ha

private lemma odd_add_of_pythagorean_param_parity {m n : ℤ}
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Odd (m + n) := by
  rcases hpar with h | h
  · exact odd_add_of_emod_zero_one h.1 h.2
  · exact odd_add_of_emod_one_zero h.1 h.2
```

If your pinned Mathlib does not have `Int.odd_iff`, a fallback direct-constructor proof is:

```lean
private lemma odd_add_of_emod_zero_one_fallback {a b : ℤ}
    (ha : a % 2 = 0) (hb : b % 2 = 1) : Odd (a + b) := by
  obtain ⟨a0, ha0⟩ := exists_eq_mul_left_of_dvd (Int.dvd_of_emod_eq_zero ha)
  obtain ⟨b0, hb0⟩ := exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hb)
  rw [sub_eq_iff_eq_add] at hb0
  subst a
  subst b
  -- The shape of `Odd` is usually definitional here.
  refine ⟨a0 + b0, ?_⟩
  ring
```

Use either `odd_add_of_emod_zero_one` or the fallback, not both with the same name.

---

## 3. Ring lemmas for the quartic bridge

These are the small algebraic facts worth adding near `pythagoreanQuarticRhs`.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace MazurProof
namespace RationalPointsN12

-- Delete this local definition if the file already has it in scope.
-- def pythagoreanQuarticRhs (m n : ℤ) : ℤ :=
--   m ^ 4 + 8 * m ^ 3 * n + 2 * m ^ 2 * n ^ 2 - 8 * m * n ^ 3 + n ^ 4

@[simp] theorem pythagoreanQuarticRhs_sq_sub_two_mul (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2
        + 4 * (m ^ 2 - n ^ 2) * (2 * m * n)
        + (2 * m * n) ^ 2
      = pythagoreanQuarticRhs m n := by
  unfold pythagoreanQuarticRhs
  ring

@[simp] theorem pythagoreanQuarticRhs_two_mul_sq_sub (m n : ℤ) :
    (2 * m * n) ^ 2
        + 4 * (2 * m * n) * (m ^ 2 - n ^ 2)
        + (m ^ 2 - n ^ 2) ^ 2
      = pythagoreanQuarticRhs m n := by
  unfold pythagoreanQuarticRhs
  ring

/-- Same legs, but with the sign of the cross term reversed. This is useful when a
local parametrization produces one leg with the opposite sign. -/
@[simp] theorem pythagoreanQuarticRhs_sq_sub_two_mul_neg_cross (m n : ℤ) :
    (m ^ 2 - n ^ 2) ^ 2
        - 4 * (m ^ 2 - n ^ 2) * (2 * m * n)
        + (2 * m * n) ^ 2
      = pythagoreanQuarticRhs m (-n) := by
  unfold pythagoreanQuarticRhs
  ring

@[simp] theorem pythagoreanQuarticRhs_two_mul_sq_sub_neg_cross (m n : ℤ) :
    (2 * m * n) ^ 2
        - 4 * (2 * m * n) * (m ^ 2 - n ^ 2)
        + (m ^ 2 - n ^ 2) ^ 2
      = pythagoreanQuarticRhs m (-n) := by
  unfold pythagoreanQuarticRhs
  ring

/-- Consumes the exact leg disjunction returned by
`PythagoreanTriple.coprime_classification`. -/
theorem quartic_rhs_from_pythagorean_legs {R S m n : ℤ}
    (hlegs :
      (R = m ^ 2 - n ^ 2 ∧ S = 2 * m * n) ∨
      (R = 2 * m * n ∧ S = m ^ 2 - n ^ 2)) :
    R ^ 2 + 4 * R * S + S ^ 2 = pythagoreanQuarticRhs m n := by
  rcases hlegs with hlegs | hlegs
  · rcases hlegs with ⟨rfl, rfl⟩
    exact pythagoreanQuarticRhs_sq_sub_two_mul m n
  · rcases hlegs with ⟨rfl, rfl⟩
    exact pythagoreanQuarticRhs_two_mul_sq_sub m n

/-- Nonzero product of the Euclidean parameters, from nonzero primitive legs. -/
theorem pythagorean_params_mul_ne_zero_of_legs {R S m n : ℤ}
    (hRS0 : R * S ≠ 0)
    (hlegs :
      (R = m ^ 2 - n ^ 2 ∧ S = 2 * m * n) ∨
      (R = 2 * m * n ∧ S = m ^ 2 - n ^ 2)) :
    m * n ≠ 0 := by
  have hR0 : R ≠ 0 := by
    intro hR
    apply hRS0
    simp [hR]
  have hS0 : S ≠ 0 := by
    intro hS
    apply hRS0
    simp [hS]
  rcases hlegs with hlegs | hlegs
  · rcases hlegs with ⟨hR, hS⟩
    intro hmn
    apply hS0
    calc
      S = 2 * m * n := hS
      _ = 2 * (m * n) := by ring
      _ = 0 := by rw [hmn]; ring
  · rcases hlegs with ⟨hR, hS⟩
    intro hmn
    apply hR0
    calc
      R = 2 * m * n := hR
      _ = 2 * (m * n) := by ring
      _ = 0 := by rw [hmn]; ring

private lemma odd_add_of_emod_zero_one {a b : ℤ}
    (ha : a % 2 = 0) (hb : b % 2 = 1) : Odd (a + b) := by
  rw [Int.odd_iff]
  rw [Int.add_emod, ha, hb]
  norm_num

private lemma odd_add_of_emod_one_zero {a b : ℤ}
    (ha : a % 2 = 1) (hb : b % 2 = 0) : Odd (a + b) := by
  rw [add_comm]
  exact odd_add_of_emod_zero_one hb ha

private lemma odd_add_of_pythagorean_param_parity {m n : ℤ}
    (hpar : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) :
    Odd (m + n) := by
  rcases hpar with h | h
  · exact odd_add_of_emod_zero_one h.1 h.2
  · exact odd_add_of_emod_one_zero h.1 h.2

end RationalPointsN12
end MazurProof
```

The two main `@[simp]` ring lemmas are intentionally oriented with the exact expression occurring after `rw [hr]` and `rw [hR, hS]`.

---

## 4. Paste-oriented proof of the requested theorem

Put this after the helpers above. It uses no axioms and no `sorry`.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace MazurProof
namespace RationalPointsN12

/-- Bridge from the primitive Pythagorean twist to the quartic RHS already used in
`RationalPointsN12.lean`.

The hypothesis `hpar : Odd (R + S)` is mathematically natural but not needed by
Mathlib's primitive classification; `hcop` and `hs` already force opposite parity
of the two legs. It is kept in the signature because upstream code supplies it. -/
theorem primitive_pythagorean_twist_to_pythagoreanQuarticRhs
    {R S r s : ℤ}
    (hRS0 : R * S ≠ 0)
    (hcop : Int.gcd R S = 1)
    (hpar : Odd (R + S))
    (hs : s ^ 2 = R ^ 2 + S ^ 2)
    (hr : r ^ 2 = R ^ 2 + 4 * R * S + S ^ 2) :
    ∃ m n : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      Odd (m + n) ∧
      r ^ 2 = pythagoreanQuarticRhs m n := by
  -- Convert `hs` into Mathlib's Pythagorean-triple predicate.
  have hpy : PythagoreanTriple R S s := by
    dsimp [PythagoreanTriple]
    calc
      R * R + S * S = R ^ 2 + S ^ 2 := by ring
      _ = s ^ 2 := hs.symm
      _ = s * s := by ring

  -- This is only to mark the supplied parity hypothesis as intentionally unused;
  -- the classification below derives the needed parameter parity itself.
  have _hpar_supplied : Odd (R + S) := hpar

  obtain ⟨m, n, hlegs, _hz, hgcd, hpar_mn⟩ :=
    (PythagoreanTriple.coprime_classification (x := R) (y := S) (z := s)).mp
      ⟨hpy, hcop⟩

  refine ⟨m, n, ?_, hgcd, ?_, ?_⟩
  · exact pythagorean_params_mul_ne_zero_of_legs hRS0 hlegs
  · exact odd_add_of_pythagorean_param_parity hpar_mn
  · rw [hr]
    exact quartic_rhs_from_pythagorean_legs hlegs

end RationalPointsN12
end MazurProof
```

### If `Int.odd_iff` is not available in the pinned Mathlib

Only the parity helper needs changing. Replace `odd_add_of_emod_zero_one` with the fallback from section 2. The rest of the theorem should remain identical.

---

## 5. Handling manual orientation/sign cases

If the existing local file already has a Pythagorean parametrization lemma that gives legs as `±(m^2-n^2)` and `±2mn`, you can still avoid redoing algebra. Use this table.

Let

```lean
A = m ^ 2 - n ^ 2
B = 2 * m * n
Q m n = pythagoreanQuarticRhs m n
```

Then:

```text
R,S are A,B in either order        -> R² + 4RS + S² = Q m n
R,S are -A,-B in either order      -> R² + 4RS + S² = Q m n
R,S are A,-B or -B,A in either order -> R² + 4RS + S² = Q m (-n)
R,S are -A,B or B,-A in either order -> R² + 4RS + S² = Q m (-n)
```

The reason is simply that changing exactly one leg reverses the cross term. The ring lemmas from section 3 prove both signs of the cross term.

A pasteable normalizer for the two useful cross-term signs is:

```lean
import Mathlib.Tactic

namespace MazurProof
namespace RationalPointsN12

/-- Same-sign Euclidean legs: either both standard, or both negated, and either order. -/
def SameSignEuclidLegs (R S m n : ℤ) : Prop :=
  (R = m ^ 2 - n ^ 2 ∧ S = 2 * m * n) ∨
  (R = 2 * m * n ∧ S = m ^ 2 - n ^ 2) ∨
  (R = -(m ^ 2 - n ^ 2) ∧ S = -(2 * m * n)) ∨
  (R = -(2 * m * n) ∧ S = -(m ^ 2 - n ^ 2))

/-- Opposite-sign Euclidean legs: exactly one of the two standard legs is negated,
with either order. -/
def OppSignEuclidLegs (R S m n : ℤ) : Prop :=
  (R = m ^ 2 - n ^ 2 ∧ S = -(2 * m * n)) ∨
  (R = -(2 * m * n) ∧ S = m ^ 2 - n ^ 2) ∨
  (R = -(m ^ 2 - n ^ 2) ∧ S = 2 * m * n) ∨
  (R = 2 * m * n ∧ S = -(m ^ 2 - n ^ 2))

theorem quartic_rhs_of_same_sign_euclid_legs {R S m n : ℤ}
    (h : SameSignEuclidLegs R S m n) :
    R ^ 2 + 4 * R * S + S ^ 2 = pythagoreanQuarticRhs m n := by
  rcases h with h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring

theorem quartic_rhs_of_opp_sign_euclid_legs {R S m n : ℤ}
    (h : OppSignEuclidLegs R S m n) :
    R ^ 2 + 4 * R * S + S ^ 2 = pythagoreanQuarticRhs m (-n) := by
  rcases h with h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring
  · rcases h with ⟨rfl, rfl⟩
    unfold pythagoreanQuarticRhs
    ring

end RationalPointsN12
end MazurProof
```

In the main proof, this pattern becomes:

```lean
rcases hsigned_legs with hsame | hopp
· refine ⟨m, n, ?mn0, hgcd, ?odd, ?quartic⟩
  · -- from the nonzero even leg
    ...
  · exact odd_add_of_pythagorean_param_parity hpar_mn
  · rw [hr]
    exact quartic_rhs_of_same_sign_euclid_legs hsame
· refine ⟨m, -n, ?mn0, ?gcd, ?odd, ?quartic⟩
  · -- `m * (-n) ≠ 0` follows from `m * n ≠ 0` by `simpa`/`ring_nf`.
    ...
  · -- `Int.gcd m (-n) = Int.gcd m n` after unfolding `Int.gcd`/`natAbs`.
    -- Usually: simpa [Int.gcd, Int.natAbs_neg] using hgcd
    ...
  · -- `Odd (m + -n)` is not automatic from opposite parity of `m,n` unless you
    -- state a helper for subtraction. Easier: prove `Odd (m - n)` by mod 2.
    ...
  · rw [hr]
    exact quartic_rhs_of_opp_sign_euclid_legs hopp
```

But again: with Mathlib's `PythagoreanTriple.coprime_classification`, the signed-normalizer branch is unnecessary because the theorem already returns exact signed integer parameters in one of the two clean orientations.

---

## 6. Recommended integration path in `RationalPointsN12.lean`

1. Add the import if not already covered by a broad import:

```lean
import Mathlib.NumberTheory.PythagoreanTriples
```

2. Add the two ring lemmas:

```lean
pythagoreanQuarticRhs_sq_sub_two_mul
pythagoreanQuarticRhs_two_mul_sq_sub
```

3. Add the leg consumer and nonzero helper:

```lean
quartic_rhs_from_pythagorean_legs
pythagorean_params_mul_ne_zero_of_legs
```

4. Add the parity helper:

```lean
odd_add_of_pythagorean_param_parity
```

5. Paste the theorem:

```lean
primitive_pythagorean_twist_to_pythagoreanQuarticRhs
```

This keeps the bridge entirely elementary from the current file's point of view: the only number-theory input is Mathlib's existing primitive Pythagorean triple classification, and the remaining obligations are `ring`, `rw`, and parity conversion.