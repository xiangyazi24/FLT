# Q2447 four integer squares AP theorem Lean route

## 1. Mathlib status

I do not see a direct Mathlib theorem named like “four integer squares in arithmetic progression are constant”.  The relevant existing Mathlib theorem is the FLT exponent-4 core:

```lean
import Mathlib.NumberTheory.FLT.Four

#check Fermat42
#check not_fermat_42
#check fermatLastTheoremFour
```

The useful theorem is:

```lean
not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 2
```

So Mathlib does not appear to provide the AP theorem directly, but it already provides the descent hard core needed to prove it.  The shortest Lean route should reduce the nonconstant four-square AP theorem to `not_fermat_42`, not reprove Fermat descent.

## 2. Recommended theorem layer

Put this in a small auxiliary file, for example:

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-- Four integer squares in arithmetic progression, written as equal first differences. -/
def IntFourSqAP (a b c d : ℤ) : Prop :=
  b^2 - a^2 = c^2 - b^2 ∧ c^2 - b^2 = d^2 - c^2

/-- Integer version of Fermat/Euler: four integer squares in AP are constant. -/
def FourIntSquaresAPConst : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2

/-- Rational version used by the N=12 route. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 →
    y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2 →
    w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2

/-- The single new hard bridge needed if using Mathlib's FLT4 theorem.

This is the theorem to prove by AP algebra / Pythagorean-triple reduction.  Once this
exists, the actual integer AP theorem is a tiny wrapper around `not_fermat_42`. -/
def FourSquaresAPToFermat42Bridge : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ (w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2) →
    ∃ a b c : ℤ,
      a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2

/-- Once the AP-to-FLT4 bridge is proved, Mathlib closes the integer theorem. -/
theorem fourIntSquaresAPConst_of_fermat42_bridge
    (hbridge : FourSquaresAPToFermat42Bridge) :
    FourIntSquaresAPConst := by
  intro w x y z hap
  by_contra hconst
  rcases hbridge hap hconst with ⟨a, b, c, ha, hb, h42⟩
  exact (not_fermat_42 ha hb) h42
```

This code has no `sorry` and gives the right interface: the remaining hard theorem is exactly `FourSquaresAPToFermat42Bridge`.

## 3. Bridge from integer AP to the rational residual

Paste the following after the Q2446 denominator-clearing file, i.e. after these names are available:

```lean
#check RatIntScale4
#check rat_int_scale4_nonempty
#check intFourSqAP_of_ratIntScale4
```

Then the rational residual follows from `FourIntSquaresAPConst` by cancellation of the common nonzero scale.

```lean
/-- If two scaled integer coordinates have equal squares, cancel the nonzero
rational scale and get equality of the original rational squares. -/
private lemma rat_sq_eq_of_scaled_sq_eq
    {M W X : ℤ} {w x : ℚ}
    (hM : M ≠ 0)
    (hW : (W : ℚ) = (M : ℚ) * w)
    (hX : (X : ℚ) = (M : ℚ) * x)
    (hWX : W ^ 2 = X ^ 2) :
    w ^ 2 = x ^ 2 := by
  have hMq : (M : ℚ) ≠ 0 := by
    exact_mod_cast hM
  have hM2 : (M : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hMq
  apply mul_left_cancel₀ hM2
  calc
    (M : ℚ) ^ 2 * w ^ 2 = ((M : ℚ) * w) ^ 2 := by ring
    _ = (W : ℚ) ^ 2 := by rw [← hW]
    _ = ((W ^ 2 : ℤ) : ℚ) := by norm_cast
    _ = ((X ^ 2 : ℤ) : ℚ) := by
          exact congrArg (fun n : ℤ => (n : ℚ)) hWX
    _ = (X : ℚ) ^ 2 := by norm_cast
    _ = ((M : ℚ) * x) ^ 2 := by rw [hX]
    _ = (M : ℚ) ^ 2 * x ^ 2 := by ring

/-- Denominator clearing plus the integer AP theorem gives the rational theorem. -/
theorem fourRatSquaresAPConst_of_fourIntSquaresAPConst
    (hInt : FourIntSquaresAPConst) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  rcases rat_int_scale4_nonempty w x y z with ⟨s⟩
  have hsap : IntFourSqAP s.W s.X s.Y s.Z :=
    intFourSqAP_of_ratIntScale4 s h1 h2
  rcases hInt hsap with ⟨hWX, hXY, hYZ⟩
  exact ⟨
    rat_sq_eq_of_scaled_sq_eq s.hM s.hW s.hX hWX,
    rat_sq_eq_of_scaled_sq_eq s.hM s.hX s.hY hXY,
    rat_sq_eq_of_scaled_sq_eq s.hM s.hY s.hZ hYZ⟩
```

The final N=12 assumption can then be discharged by:

```lean
theorem fourRatSquaresAPConst_from_fermat42_bridge
    (hbridge : FourSquaresAPToFermat42Bridge) :
    FourRatSquaresAPConst := by
  exact fourRatSquaresAPConst_of_fourIntSquaresAPConst
    (fourIntSquaresAPConst_of_fermat42_bridge hbridge)
```

## 4. What should the hard core be?

Best route: **reduce to Mathlib's `not_fermat_42`**.  Do not reprove Fermat descent inside `RationalPointsN12.lean`.  The Mathlib file `Mathlib.NumberTheory.FLT.Four` already contains the infinite descent for `a^4 + b^4 = c^2`, and the AP theorem should be a wrapper around it.

The clean hard target is therefore:

```lean
FourSquaresAPToFermat42Bridge
```

Implementation choices for that bridge:

1. **Pythagorean-triple route, preferred if staying elementary.**
   Convert a nonconstant four-square AP into the standard Fermat right-triangle obstruction, then into `a^4 + b^4 = c^2`.  This should use:

   ```lean
   import Mathlib.NumberTheory.PythagoreanTriples
   import Mathlib.NumberTheory.FLT.Four

   #check PythagoreanTriple
   #check PythagoreanTriple.coprime_classification'
   #check not_fermat_42
   ```

   This is the most compatible route with Mathlib, because `not_fermat_42` itself is proved from Pythagorean-triple descent.

2. **Quartic residual route, acceptable only if the local `QuarticDescent.lean` already proves the Ljunggren/Eisenstein nontrivial quartic.**
   Use this route only if the local repo already has a theorem with a shape like:

   ```lean
   def QuarticAConst : Prop :=
     ∀ {m n c : ℤ},
       m ≠ 0 → n ≠ 0 →
       Nat.Coprime m.natAbs n.natAbs →
       c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
       m ^ 2 = n ^ 2
   ```

   Then isolate the AP-to-quartic bridge as:

   ```lean
   def FourSquaresAPToQuarticABridge : Prop :=
     ∀ {w x y z : ℤ},
       IntFourSqAP w x y z →
       ¬ (w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2) →
       ∃ m n c : ℤ,
         m ≠ 0 ∧ n ≠ 0 ∧
         Nat.Coprime m.natAbs n.natAbs ∧
         c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 ∧
         m ^ 2 ≠ n ^ 2
   ```

   This is more work unless `QuarticDescent.lean` already has the final constant/classification theorem.  `QuarticDescentN16.lean` is not the shortest dependency for N=12 four-square AP; keep it out unless a theorem is already imported there.

## 5. Recommended file structure

Shortest low-cycle structure:

```text
FLT/Assumptions/MazurProof/FourSquaresAP.lean
  imports Mathlib.NumberTheory.FLT.Four
  defines IntFourSqAP, FourIntSquaresAPConst, FourSquaresAPToFermat42Bridge
  proves fourIntSquaresAPConst_of_fermat42_bridge

FLT/Assumptions/MazurProof/N12APNorm.lean
  imports FourSquaresAP.lean and the Q2446 denominator-clearing code
  proves fourRatSquaresAPConst_of_fourIntSquaresAPConst

FLT/Assumptions/MazurProof/RationalPointsN12.lean
  imports N12APNorm.lean
  consumes FourRatSquaresAPConst
```

This keeps the genuine mathematical frontier explicit and small: prove `FourSquaresAPToFermat42Bridge`, then everything from integer AP to the rational residual is routine Lean algebra and denominator clearing.
