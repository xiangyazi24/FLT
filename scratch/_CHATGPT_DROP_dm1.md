# Q1353 (dm1/dm2): status of a complete `quartic_plus` proof

I cannot honestly give a closed, compilable Lean proof of this theorem in 200 lines from the current repository and Mathlib API. The repository search index does not show a local `quartic_plus` / `QuarticPlus` theorem or the required factor-splitting and Pythagorean descent lemmas. Mathlib has `PythagoreanTriple.coprime_classification'`, but it does **not** contain the whole Ljunggren-style descent theorem as a packaged result.

A fake answer with `axiom`, `admit`, or `sorry` would compile in this repo because `warn.sorry = false`, but it would not be the requested proof. The honest boundary is: the strong-induction wrapper is short and fully compilable; the arithmetic descent step is the real missing proof.

## Fully compilable strong-induction wrapper

This is the exact structure you want. It is written over `ℤ` and uses `B.natAbs` as the induction measure.

```lean
import Mathlib

namespace DM2

/-- Integer version of the quartic-plus equation. -/
def QuarticPlusZ (r B s : ℤ) : Prop :=
  0 < r ∧ 0 < B ∧ Int.gcd r B = 1 ∧
    s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

/-- The base conclusion. -/
def BaseZ (r B : ℤ) : Prop :=
  r = 1 ∧ B = 1

/--
The descent step you must prove arithmetically: every non-base positive primitive
solution gives a smaller non-base positive primitive solution.
-/
def QuarticPlusDescentStepZ : Prop :=
  ∀ {r B s : ℤ}, QuarticPlusZ r B s → ¬ BaseZ r B →
    ∃ r' B' s' : ℤ,
      QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < B.natAbs

/-- Once the descent step is available, the theorem follows by strong induction on `B.natAbs`. -/
theorem quartic_plus_from_descent
    (desc : QuarticPlusDescentStepZ)
    {r B s : ℤ} (hsol : QuarticPlusZ r B s) :
    r = 1 ∧ B = 1 := by
  classical
  have hmain : BaseZ r B := by
    refine
      (Nat.strong_induction_on
        (p := fun N : ℕ =>
          ∀ r B s : ℤ, B.natAbs = N → QuarticPlusZ r B s → BaseZ r B)
        B.natAbs ?_) r B s rfl hsol
    intro N ih r B s hBN hsol
    by_cases hbase : BaseZ r B
    · exact hbase
    · rcases desc hsol hbase with ⟨r', B', s', hsol', hnot', hlt'⟩
      have hltN : B'.natAbs < N := by
        simpa [hBN] using hlt'
      exact False.elim (hnot' (ih B'.natAbs hltN r' B' s' rfl hsol'))
  exact hmain

end DM2
```

## The missing theorem

The real target is not the wrapper above but this lemma:

```lean
namespace DM2

theorem quartic_plus_descent_step : QuarticPlusDescentStepZ := by
  intro r B s hsol hnonbase
  -- 1. Prove r and B odd by mod 4 analysis.
  -- 2. Define U = 2*r^2 + B^2 - 2*s and V = 2*r^2 + B^2 + 2*s.
  -- 3. Prove U*V = 5*B^4, U,V positive, coprime, odd.
  -- 4. Split the coprime odd factors of 5*B^4 into (a^4, 5*b^4) or (5*a^4, b^4).
  -- 5. In the (a^4,5*b^4) branch derive:
  --      4*r^2 = (a^2-b^2)^2 + 4*b^4.
  -- 6. Let h = (a^2-b^2)/2; prove h^2 + b^4 = r^2.
  -- 7. Use `PythagoreanTriple.coprime_classification'` on the oriented triple
  --      PythagoreanTriple ((b:ℤ)^2) h r
  --    because the first leg must be the odd one.
  -- 8. Split (m-n)(m+n)=b^2 into m-n=u^2 and m+n=v^2 using
  --      Int.sq_of_gcd_eq_one.
  -- 9. Return the smaller solution (v,u,a), or the analogous branch solution.
  -- This is several hundred lines of arithmetic, not currently a Mathlib one-liner.
  sorry

end DM2
```

## Why the complete 200-line request is not realistic

The requested proof needs at least these nontrivial local lemmas:

```lean
-- parity / mod 4 preparation
lemma quarticPlus_odd_rB : ...

-- U,V preparation
lemma UV_factorization : ...
lemma UV_coprime : ...
lemma UV_odd : ...
lemma UV_positive : ...

-- coprime factor split of 5*B^4
lemma split_five_mul_fourth_coprime_odd : ...

-- Pythagorean square-leg descent
lemma pythagorean_square_leg_descent : ...

-- branch algebra returning a smaller non-base QuarticPlus solution
lemma descent_branch_a4_5b4 : ...
lemma descent_branch_5a4_b4 : ...
```

Only after those exist does the final theorem become the short wrapper `quartic_plus_from_descent` above.

## Practical next step

Formalize the descent step as a separate theorem first:

```lean
lemma quartic_plus_descent_step : QuarticPlusDescentStepZ := by
  ...
```

Then the final theorem is just:

```lean
theorem quartic_plus
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r = 1 ∧ B = 1 := by
  exact quartic_plus_from_descent
    quartic_plus_descent_step
    ⟨hr, hB, hgcd, heq⟩
```
