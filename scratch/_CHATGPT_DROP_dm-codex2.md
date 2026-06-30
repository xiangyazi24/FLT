# Q2445 Int square_factor_balance Lean code

Place this after the already-proved `nat_square_factor_balance` theorem, in the same namespace or with the theorem name qualified.

```lean
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.Lemmas

namespace EulerAux

#check Int.isCoprime_iff_nat_coprime
#check Int.natAbs_mul
#check Int.natAbs_pow
#check Int.natAbs_eq_zero
#check Int.natAbs_inj_of_nonneg_of_nonneg

/-- Convert integer coprimality to the Nat coprimality shape expected by
`nat_square_factor_balance`. -/
theorem nat_coprime_natAbs_of_isCoprime_int {a b : ℤ}
    (h : IsCoprime a b) :
    Nat.Coprime a.natAbs b.natAbs :=
  Int.isCoprime_iff_nat_coprime.mp h

/-- Positive integers have nonzero `natAbs`. -/
theorem natAbs_ne_zero_of_pos {z : ℤ} (hz : 0 < z) :
    z.natAbs ≠ 0 := by
  intro hz0
  exact (ne_of_gt hz) (Int.natAbs_eq_zero.mp hz0)

/-- Taking `natAbs` of the integer balance equation gives the Nat balance equation. -/
theorem natAbs_square_balance_eq
    {b c M N : ℤ}
    (h : b^2 * M = c^2 * N) :
    b.natAbs^2 * M.natAbs = c.natAbs^2 * N.natAbs := by
  have h' := congrArg Int.natAbs h
  simpa [Int.natAbs_mul, Int.natAbs_pow] using h'

/-- Cast back from a positive integer whose `natAbs` is a square. -/
theorem int_eq_sq_of_pos_of_natAbs_eq_sq_natAbs
    {x y : ℤ}
    (hx : 0 < x)
    (hxy : x.natAbs = y.natAbs^2) :
    x = y^2 := by
  have hxy' : x.natAbs = (y^2).natAbs := by
    simpa [Int.natAbs_pow] using hxy
  exact (Int.natAbs_inj_of_nonneg_of_nonneg
    (le_of_lt hx) (sq_nonneg y)).mp hxy'

/-- Cleaner wrapper if the local context already has Nat coprimality of `natAbs`s. -/
theorem square_factor_balance_int_natAbs
    {b c M N : ℤ}
    (hb : 0 < b) (hc : 0 < c) (hM : 0 < M) (hN : 0 < N)
    (hbc : Nat.Coprime b.natAbs c.natAbs)
    (hMN : Nat.Coprime M.natAbs N.natAbs)
    (h : b^2 * M = c^2 * N) :
    M = c^2 ∧ N = b^2 := by
  have hb0 : b.natAbs ≠ 0 := natAbs_ne_zero_of_pos hb
  have hc0 : c.natAbs ≠ 0 := natAbs_ne_zero_of_pos hc
  have hnat : b.natAbs^2 * M.natAbs = c.natAbs^2 * N.natAbs :=
    natAbs_square_balance_eq h
  rcases nat_square_factor_balance hb0 hc0 hbc hMN hnat with ⟨hMabs, hNabs⟩
  exact ⟨
    int_eq_sq_of_pos_of_natAbs_eq_sq_natAbs hM hMabs,
    int_eq_sq_of_pos_of_natAbs_eq_sq_natAbs hN hNabs⟩

/-- Desired EulerAux integer wrapper.  No statement change is needed: `IsCoprime` over
`ℤ` converts directly to `Nat.Coprime` of `natAbs`s via
`Int.isCoprime_iff_nat_coprime`. -/
theorem square_factor_balance_int
    {b c M N : ℤ}
    (hb : 0 < b) (hc : 0 < c) (hM : 0 < M) (hN : 0 < N)
    (hbc : IsCoprime b c) (hMN : IsCoprime M N)
    (h : b^2 * M = c^2 * N) :
    M = c^2 ∧ N = b^2 := by
  exact square_factor_balance_int_natAbs hb hc hM hN
    (nat_coprime_natAbs_of_isCoprime_int hbc)
    (nat_coprime_natAbs_of_isCoprime_int hMN)
    h

end EulerAux
```

If `nat_square_factor_balance` is not in namespace `EulerAux`, replace the call by its qualified name. The desired `IsCoprime` theorem itself does not need to be changed.
