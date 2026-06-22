import scratch.WardSomos
import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Ward's theorem: `IsEllSequence (normEDS b c d)` (the open Mathlib TODO)

Step 1 (this file, PROVEN): the full 3-variable `IsEllSequence` reduces to the 2-variable
addition formula `AddRel` by a pure `linear_combination` (CAS-verified signs:
`Ell(m,n,r) = -W(n)²·AddRel(m,r) + W(m)²·AddRel(n,r) + W(r)²·AddRel(m,n)`).

Step 2 (`normEDS_addRel`, the remaining hard part): prove `AddRel (normEDS b c d) m n` for all
`m n` by gap induction on `n` (base cases n=0,1,2 — n=2 is `normEDS_adjacent_somos`).
-/

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The two-variable addition formula = `IsEllSequence` at `r = 1` (using `W 1 = 1`). -/
def AddRel (W : ℤ → R) (m n : ℤ) : Prop :=
  W (m + n) * W (m - n) = W (m + 1) * W (m - 1) * W n ^ 2 - W (n + 1) * W (n - 1) * W m ^ 2

/-- **Step 1.** The full three-variable Ward identity follows from the two-variable addition
formula by pure algebra (no `W 1 = 1` needed — it is an identity in free sequence values). -/
theorem isEllSequence_of_addRel {W : ℤ → R} (hAdd : ∀ m n : ℤ, AddRel W m n) :
    IsEllSequence W := by
  intro m n r
  have hmr := hAdd m r
  have hnr := hAdd n r
  have hmn := hAdd m n
  unfold AddRel at hmr hnr hmn
  linear_combination (- W n ^ 2) * hmr + (W m ^ 2) * hnr + (W r ^ 2) * hmn

/-- **Step 2 (remaining).** `normEDS` satisfies the two-variable addition formula.
Gap induction on `n`; base case `n = 2` is `normEDS_adjacent_somos`. -/
theorem normEDS_addRel (b c d : R) (m n : ℤ) : AddRel (normEDS b c d) m n := by
  sorry

/-- **Ward's theorem** (the Mathlib TODO): `normEDS` is an elliptic sequence. -/
theorem normEDS_isEllSequence (b c d : R) : IsEllSequence (normEDS b c d) :=
  isEllSequence_of_addRel (normEDS_addRel b c d)

end FLT.EDS
