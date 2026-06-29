# Q2292: Lean helper for coprime product square

Target file: `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.

This drop answers the **coprime product square** helper request, not QuarticA/QuarticB content.  The main recommendation is to prove the Nat helper using the existing Mathlib theorem

```lean
exists_eq_pow_of_mul_eq_pow
```

from `Mathlib.Algebra.GCDMonoid.Basic`, then pass to integers with `Int.natAbs` and the nonnegativity hypotheses.

## Lean code first

```lean
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic

/-- Natural-number helper: coprime factors of a square are squares.

This is the shortest route in current Mathlib.  The key imported theorem is
`exists_eq_pow_of_mul_eq_pow`, specialized to `α := ℕ` and `k := 2`.
It handles zero cases automatically: if one Nat factor is zero and the factors
are coprime, the other factor is forced to be `1`, hence a square. -/
theorem Nat_coprime_mul_eq_sq
    {a b z : ℕ}
    (hcop : Nat.Coprime a b)
    (h : a * b = z ^ 2) :
    ∃ r s : ℕ, a = r ^ 2 ∧ b = s ^ 2 := by
  have hgcd : IsUnit (GCDMonoid.gcd a b) := by
    rw [gcd_eq_nat_gcd, hcop.gcd_eq_one]
    exact isUnit_one
  obtain ⟨r, hr⟩ :=
    exists_eq_pow_of_mul_eq_pow
      (α := ℕ) (a := a) (b := b) (c := z) (k := 2) hgcd h

  have hgcd' : IsUnit (GCDMonoid.gcd b a) := by
    rw [gcd_eq_nat_gcd, Nat.gcd_comm, hcop.gcd_eq_one]
    exact isUnit_one
  have h' : b * a = z ^ 2 := by
    simpa [mul_comm] using h
  obtain ⟨s, hs⟩ :=
    exists_eq_pow_of_mul_eq_pow
      (α := ℕ) (a := b) (b := a) (c := z) (k := 2) hgcd' h'

  exact ⟨r, s, hr, hs⟩

/-- Integer wrapper: nonnegative coprime integer factors of a square are squares.

The hypotheses `ha` and `hb` are exactly what lets us convert back from
`natAbs` without introducing signs.  This is the version wanted by the N=12
quartic residual split lemmas. -/
theorem Int_coprime_mul_eq_sq_of_nonneg
    {a b z : ℤ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hcop : Int.gcd a b = 1)
    (h : a * b = z ^ 2) :
    ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2 := by
  have hcopNat : Nat.Coprime a.natAbs b.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd_eq_natAbs] using hcop

  have hnat : a.natAbs * b.natAbs = z.natAbs ^ 2 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs h

  obtain ⟨r, s, hr, hs⟩ := Nat_coprime_mul_eq_sq hcopNat hnat
  refine ⟨(r : ℤ), (s : ℤ), ?_, ?_⟩
  · have ha_abs : (a.natAbs : ℤ) = a := by
      rw [Int.natCast_natAbs, abs_of_nonneg ha]
    rw [← ha_abs, hr]
    norm_num
  · have hb_abs : (b.natAbs : ℤ) = b := by
      rw [Int.natCast_natAbs, abs_of_nonneg hb]
    rw [← hb_abs, hs]
    norm_num
```

If the `Nat.Coprime` rewrite is sticky in the local file because of namespace/import differences, replace only the proof of `hcopNat` by this equivalent version:

```lean
  have hcopNat : Nat.Coprime a.natAbs b.natAbs := by
    change Nat.gcd a.natAbs b.natAbs = 1
    simpa [Int.gcd_eq_natAbs] using hcop
```

## Exact theorem/API facts used

Add these temporary checks near the new helper while integrating:

```lean
#check exists_eq_pow_of_mul_eq_pow
#check gcd_eq_nat_gcd
#check Int.gcd_eq_natAbs
#check Int.natAbs_mul
#check Int.natAbs_pow
#check Int.natCast_natAbs
#check Nat.Coprime.gcd_eq_one
#check Nat.coprime_iff_gcd_eq_one
```

Expected key theorem shape:

```lean
-- In `Mathlib.Algebra.GCDMonoid.Basic`:
-- theorem exists_eq_pow_of_mul_eq_pow
--     [GCDMonoid α] [Subsingleton αˣ]
--     {a b c : α}
--     (hab : IsUnit (gcd a b))
--     {k : ℕ}
--     (h : a * b = c ^ k) :
--     ∃ d : α, a = d ^ k
```

For `α := ℕ`, the hypotheses `[GCDMonoid ℕ]` and `[Subsingleton ℕˣ]` are already available after importing `Mathlib.Algebra.GCDMonoid.Nat`.  The helper calls the theorem twice: once for `a`, once after commuting the product for `b`.

## Grep patterns

From the repository root:

```bash
grep -R "theorem exists_eq_pow_of_mul_eq_pow" .lake/packages/mathlib/Mathlib/Algebra/GCDMonoid/Basic.lean
grep -R "theorem gcd_eq_nat_gcd" .lake/packages/mathlib/Mathlib/Algebra/GCDMonoid/Nat.lean
grep -R "theorem gcd_eq_natAbs" .lake/packages/mathlib/Mathlib/Algebra/GCDMonoid/Nat.lean
grep -R "natAbs_pow" .lake/packages/mathlib/Mathlib/Data/Int*.lean .lake/packages/mathlib/Mathlib/Data/Int -n
grep -R "gcd_eq_one" .lake/packages/mathlib/Mathlib/Data/Nat/GCD .lake/packages/mathlib/Mathlib/Data/Nat -n
```

The pinned project manifest on `ai-scratch` uses Mathlib commit `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; at that revision, `Mathlib.Algebra.GCDMonoid.Nat` imports `Mathlib.Algebra.GCDMonoid.Basic` and provides the `GCDMonoid`/`NormalizedGCDMonoid` instances for both `ℕ` and `ℤ`.

## Why this is robust for zero cases

No manual zero split is needed.

In the Nat helper, if `a = 0`, `Nat.Coprime a b` forces `b = 1`.  The equation `a * b = z ^ 2` forces `z = 0`, and `exists_eq_pow_of_mul_eq_pow` returns `a = 0 ^ 2`.  The swapped call then returns `b = 1 ^ 2`.  The case `b = 0` is symmetric.

In the Int wrapper, `ha : 0 ≤ a` and `hb : 0 ≤ b` ensure that `a = (a.natAbs : ℤ)` and `b = (b.natAbs : ℤ)`.  Thus the Nat result lifts back without sign ambiguity.  Without the nonnegativity hypotheses, the statement is false as written: for example `a = -1`, `b = -1`, `z = 1` has `a * b = z ^ 2`, but neither negative factor is an integer square.

## Where to place it

Put the helper before the QuarticA/QuarticB split lemmas, near other elementary integer lemmas.  It is not specific to N=12, so a neutral local name like the requested

```lean
Int_coprime_mul_eq_sq_of_nonneg
```

is fine.  If the file already has a namespace for Mazur/N12 helpers, move both theorem names inside that namespace and keep the statements unchanged.
