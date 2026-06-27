# Q1364 (dm1/dm3): strong induction skeleton for `quartic_plus`

The induction measure should be `B.natAbs`.  The one correction is important: the descent step must return a smaller **non-base** solution.  If it only returns a smaller solution, strong induction gives that the smaller solution is base, but that does not contradict anything.

Below is the clean skeleton.  The only `sorry` is the arithmetic descent step.

```lean
import Mathlib

namespace DM3

/-- Integer form of the quartic-plus equation. -/
def QuarticPlusZ (r B s : ℤ) : Prop :=
  0 < r ∧ 0 < B ∧ Int.gcd r B = 1 ∧
    s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4

/-- The desired base conclusion. -/
def BaseZ (r B : ℤ) : Prop :=
  r = 1 ∧ B = 1

/--
The descent step needed by the strong-induction wrapper.

It must produce a smaller non-base solution, not merely a smaller solution.
-/
def QuarticPlusDescentStepZ : Prop :=
  ∀ {r B s : ℤ},
    QuarticPlusZ r B s → ¬ BaseZ r B →
      ∃ r' B' s' : ℤ,
        QuarticPlusZ r' B' s' ∧ ¬ BaseZ r' B' ∧ B'.natAbs < B.natAbs

/-- Arithmetic descent step: this is where the factorization and Pythagorean descent go. -/
theorem quartic_plus_descent_step : QuarticPlusDescentStepZ := by
  intro r B s hsol hnonbase
  -- Prove the oddness, define U,V, split `U*V = 5*B^4`,
  -- run the Pythagorean square-leg descent, and return a smaller non-base solution.
  sorry

/-- Strong-induction closure on `B.natAbs`. -/
theorem quartic_plus_from_descent
    (desc : QuarticPlusDescentStepZ)
    {r B s : ℤ} (hsol : QuarticPlusZ r B s) :
    BaseZ r B := by
  classical

  let P : ℕ → Prop :=
    fun N => ∀ r B s : ℤ, B.natAbs = N → QuarticPlusZ r B s → BaseZ r B

  have hP : P B.natAbs := by
    refine Nat.strongRecOn (motive := P) B.natAbs ?_
    intro N ih r B s hBN hsol

    -- Optional sanity check: the `N=0` case is impossible because `0 < B`.
    -- It is not needed for the proof, but useful when debugging goals.
    have hNpos : 0 < N := by
      have hBpos : 0 < B := hsol.2.1
      by_contra hNnot
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hNnot
      have hBabs0 : B.natAbs = 0 := by simpa [hBN, hN0]
      have hB0 : B = 0 := Int.natAbs_eq_zero.mp hBabs0
      linarith

    by_cases hbase : BaseZ r B
    · exact hbase
    · rcases desc hsol hbase with ⟨r', B', s', hsol', hnot', hlt'⟩
      have hltN : B'.natAbs < N := by
        simpa [hBN] using hlt'
      have hbase' : BaseZ r' B' := ih B'.natAbs hltN r' B' s' rfl hsol'
      exact False.elim (hnot' hbase')

  exact hP r B s rfl hsol

/-- Final user-facing theorem. -/
theorem quartic_plus
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r = 1 ∧ B = 1 := by
  exact quartic_plus_from_descent
    quartic_plus_descent_step
    ⟨hr, hB, hgcd, heq⟩

end DM3
```

If you want the descent step signature to omit `¬ BaseZ r' B'`, the wrapper cannot close.  In that weaker form, the induction only proves the smaller solution is base; you still need an additional lemma saying the constructed smaller solution is not base.  It is cleaner to include non-baseness in `QuarticPlusDescentStepZ` directly.
