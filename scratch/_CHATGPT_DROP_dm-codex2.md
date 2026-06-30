# Q2315 (dm-codex2): `CoprimeSquareProductExtraction`

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- If coprime integer squares have gcd `1`, then the roots have gcd `1`. -/
theorem int_gcd_eq_one_of_sq_gcd_eq_one {m n : ℤ}
    (h : Int.gcd (m ^ 2) (n ^ 2) = 1) :
    Int.gcd m n = 1 := by
  have hpow : (m.natAbs ^ 2).Coprime (n.natAbs ^ 2) := by
    simpa [Nat.Coprime, Int.gcd_def, pow_two] using h
  have hleft : m.natAbs.Coprime (n.natAbs ^ 2) := by
    exact
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 2)
        m.natAbs (n.natAbs ^ 2)).mp hpow
  have hmn : m.natAbs.Coprime n.natAbs := by
    exact
      (Nat.coprime_pow_right_iff (by norm_num : 0 < 2)
        m.natAbs n.natAbs).mp hleft
  simpa [Nat.Coprime, Int.gcd_def] using hmn

/-- Nonzero roots from a nonzero square factor. -/
theorem int_sq_factor_root_ne_zero {a m : ℤ}
    (ha0 : a ≠ 0) (ha : a = m ^ 2) :
    m ≠ 0 := by
  intro hm
  exact ha0 (by
    calc
      a = m ^ 2 := ha
      _ = 0 := by simp [hm])

/-- Nonzero roots from a nonzero negative square factor. -/
theorem int_neg_sq_factor_root_ne_zero {a m : ℤ}
    (ha0 : a ≠ 0) (ha : a = -(m ^ 2)) :
    m ≠ 0 := by
  intro hm
  exact ha0 (by
    calc
      a = -(m ^ 2) := ha
      _ = 0 := by simp [hm])

/--
Coprime square-product extraction with signs.

From `a*b = v^2` and `a*b ≠ 0`, the product is positive, so `a,b` are
both positive or both negative.  In the positive branch, apply the existing
nonnegative helper to `a,b`.  In the negative branch, apply it to `-a,-b`.
-/
theorem coprimeSquareProductExtraction : CoprimeSquareProductExtraction := by
  intro v a b hab0 hcop hsq
  have ha0 : a ≠ 0 := by
    intro ha
    exact hab0 (by simp [ha])
  have hb0 : b ≠ 0 := by
    intro hb
    exact hab0 (by simp [hb])
  have hv0 : v ≠ 0 := by
    intro hv
    exact hab0 (by simpa [hv] using hsq)
  have hprod_pos : 0 < a * b := by
    simpa [hsq] using (sq_pos_of_ne_zero v hv0)
  rcases (mul_pos_iff.mp hprod_pos) with hpos | hneg
  · rcases hpos with ⟨ha_pos, hb_pos⟩
    rcases int_coprime_mul_eq_sq_of_nonneg
        (a := a) (b := b) (z := v)
        (le_of_lt ha_pos) (le_of_lt hb_pos) hcop hsq with
      ⟨m, n, ha_sq, hb_sq⟩
    have hm0 : m ≠ 0 := int_sq_factor_root_ne_zero ha0 ha_sq
    have hn0 : n ≠ 0 := int_sq_factor_root_ne_zero hb0 hb_sq
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    have hmn_coprime : Int.gcd m n = 1 :=
      int_gcd_eq_one_of_sq_gcd_eq_one (by
        simpa [ha_sq, hb_sq] using hcop)
    exact ⟨m, n, hmn0, hmn_coprime, Or.inl ⟨ha_sq, hb_sq⟩⟩
  · rcases hneg with ⟨ha_neg, hb_neg⟩
    have hcop_neg : Int.gcd (-a) (-b) = 1 := by
      simpa [Int.gcd_def] using hcop
    have hsq_neg : (-a) * (-b) = v ^ 2 := by
      simpa using hsq
    rcases int_coprime_mul_eq_sq_of_nonneg
        (a := -a) (b := -b) (z := v)
        (neg_nonneg.mpr (le_of_lt ha_neg))
        (neg_nonneg.mpr (le_of_lt hb_neg)) hcop_neg hsq_neg with
      ⟨m, n, hma_sq, hmb_sq⟩
    have ha_sq : a = -(m ^ 2) := by
      rw [← hma_sq]
      ring
    have hb_sq : b = -(n ^ 2) := by
      rw [← hmb_sq]
      ring
    have hm0 : m ≠ 0 := int_neg_sq_factor_root_ne_zero ha0 ha_sq
    have hn0 : n ≠ 0 := int_neg_sq_factor_root_ne_zero hb0 hb_sq
    have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
    have hmn_coprime : Int.gcd m n = 1 :=
      int_gcd_eq_one_of_sq_gcd_eq_one (by
        simpa [hma_sq, hmb_sq] using hcop_neg)
    exact ⟨m, n, hmn0, hmn_coprime, Or.inr ⟨ha_sq, hb_sq⟩⟩

end MazurProof.RationalPointsN12
```

The only nontrivial library-dependent micro-lemma is `int_gcd_eq_one_of_sq_gcd_eq_one`.  It reduces `Int.gcd` to `Nat.gcd` via `Int.gcd_def`, uses `Nat.coprime_pow_left_iff` and `Nat.coprime_pow_right_iff`, then converts back to `Int.gcd`.

The sign split in the main theorem is deliberately by `mul_pos_iff`: after `a*b = v^2` and `a*b ≠ 0`, `v ≠ 0`, hence `0 < v^2`, hence `0 < a*b`.  The negative branch uses `(-a)*(-b) = v^2` and `Int.gcd (-a) (-b) = 1`, both discharged by `simpa`/`Int.gcd_def`.
