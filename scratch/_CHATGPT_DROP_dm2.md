# Lean drop: `clearing_denominators_gives_quartic`

This version isolates exactly the Rat-lowest-terms / valuation package.  The top-level theorem proves the easy rational clearing step with `field_simp`/`ring`, then hands the prime-exponent bookkeeping to a single helper.  I also split off the final `gcd(p,d)=1` proof from `q=d.natAbs^2`, since that part is not valuation-heavy.

```lean
import Mathlib

namespace ScratchDenominator

/--
If `q` is coprime to `p` and `q = |d|^2`, then `p` is coprime to `d`.
This is the final, non-valuation gcd cleanup.
-/
lemma int_gcd_eq_one_of_natAbs_square_eq
    {p d : ℤ} {q : ℕ}
    (hpq : Nat.Coprime p.natAbs q)
    (hq_square : q = d.natAbs ^ 2) :
    Int.gcd p d = 1 := by
  have hd_dvd_q : d.natAbs ∣ q := by
    refine ⟨d.natAbs, ?_⟩
    rw [hq_square, pow_two]
  have hcop_pd : Nat.Coprime p.natAbs d.natAbs :=
    hpq.coprime_dvd_right hd_dvd_q
  simpa [Int.gcd] using hcop_pd.gcd_eq_one

/--
The isolated Rat-lowest-terms / valuation package.

Input already has the easy rational clearing:

`w^2 = N / q^3`, where `N = p * (p^2 + p*q - q^2)`.

Mathematical content hidden by the two `sorry`s below:

1. Write `w = A / B` in lowest terms and cross-multiply to get
   `A^2 * q^3 = B^2 * N`.
2. For each prime `ℓ ∣ q`, prove `ℓ ∤ N` from
   `N ≡ p^3 [ZMOD ℓ]` and `Nat.Coprime p.natAbs q`.
3. Compare exponents in `A^2 * q^3 = B^2 * N`, forcing every exponent
   of `q` to be even, so `q = d^2`.
4. The same exponent comparison gives `B = d^3`; then `A^2 = N`, rewritten
   with `q = d^2`, gives the desired quartic equation.
-/
lemma lowest_terms_valuation_package
    (p : ℤ) (q : ℕ)
    (hq : 2 ≤ q)
    (hpq : Nat.Coprime p.natAbs q)
    (w : ℚ)
    (hclear :
      w ^ 2 =
        (((p * (p ^ 2 + p * (q : ℤ) - (q : ℤ) ^ 2) : ℤ) : ℚ) /
          (q : ℚ) ^ 3)) :
    ∃ d a : ℤ,
      2 ≤ d ∧
      q = d.natAbs ^ 2 ∧
      a ^ 2 = p * (p ^ 2 + p * d ^ 2 - d ^ 4) := by
  classical
  let A : ℤ := w.num
  let B : ℤ := (w.den : ℤ)
  let N : ℤ := p * (p ^ 2 + p * (q : ℤ) - (q : ℤ) ^ 2)

  have hB_pos : 0 < B := by
    dsimp [B]
    exact_mod_cast w.den_pos

  have hAB_coprime : Nat.Coprime A.natAbs B.natAbs := by
    dsimp [A, B]
    simpa [Int.natAbs_natCast] using w.reduced

  have hclear_int : A ^ 2 * (q : ℤ) ^ 3 = B ^ 2 * N := by
    /-
    Lowest-terms clearing step.

    From `hclear` and `w = A / B`, prove
      `A^2 * q^3 = B^2 * N`.

    Useful facts/API:
      * `Rat.num_divInt_den w` rewrites `w.num /. w.den = w`.
      * `Rat.num_div_den` rewrites `((w.num : ℚ) / w.den) = w` in some files.
      * `Rat.eq_iff_mul_eq_mul` is often the cleanest cross-multiplication lemma.
      * `hB_pos`, `hq : 2 ≤ q` discharge nonzero denominators.
    -/
    sorry

  have hvaluation :
      ∃ d : ℤ,
        2 ≤ d ∧
        q = d.natAbs ^ 2 ∧
        A ^ 2 = p * (p ^ 2 + p * d ^ 2 - d ^ 4) := by
    /-
    Prime-exponent / valuation step.

    The intended proof is exactly:
      * For prime `ℓ ∣ q`, show `ℓ ∤ N` because
        `N ≡ p * (p^2 + p*0 - 0) = p^3 [ZMOD ℓ]`, and `ℓ ∤ p` follows from
        `hpq` and `ℓ ∣ q`.
      * In `A^2 * q^3 = B^2 * N`, use `gcd(A,B)=1` and `ℓ ∤ N` to compare
        exponents:
          `3 * v_ℓ(q) = 2 * v_ℓ(B)`.
      * Hence `v_ℓ(q)` is even for all `ℓ`, so `q = d^2` with `d ≥ 2`.
      * Then `v_ℓ(B) = 3 * v_ℓ(d)`, so `B = d^3 * m`.
      * After cancelling, `A^2 = m^2 * N`; coprimality forces `m = 1`.
      * Rewrite `N` using `q = d^2`.
    -/
    sorry

  rcases hvaluation with ⟨d, hd, hq_square, hA⟩
  exact ⟨d, A, hd, hq_square, hA⟩

/--
Clearing denominators gives the denominator quartic.

This is stated with `Nat.Coprime p.natAbs q`; if your local hypothesis is
`Nat.gcd p.natAbs q = 1`, convert it with the usual `Nat.coprime_iff_gcd_eq_one`.
-/
theorem clearing_denominators_gives_quartic
    (p : ℤ) (q : ℕ)
    (hq : 2 ≤ q)
    (hpq : Nat.Coprime p.natAbs q)
    (w : ℚ)
    (hw :
      w ^ 2 =
        (p : ℚ) / (q : ℚ) *
          (((p : ℚ) ^ 2) / (q : ℚ) ^ 2 + (p : ℚ) / (q : ℚ) - 1)) :
    ∃ d a : ℤ,
      2 ≤ d ∧
      q = d.natAbs ^ 2 ∧
      a ^ 2 = p * (p ^ 2 + p * d ^ 2 - d ^ 4) ∧
      Int.gcd p d = 1 := by
  classical
  have hq_pos : 0 < q := by omega
  have hq0Q : (q : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hq_pos)

  have hclear_rat :
      w ^ 2 =
        (((p * (p ^ 2 + p * (q : ℤ) - (q : ℤ) ^ 2) : ℤ) : ℚ) /
          (q : ℚ) ^ 3) := by
    calc
      w ^ 2
          = (p : ℚ) / (q : ℚ) *
              (((p : ℚ) ^ 2) / (q : ℚ) ^ 2 + (p : ℚ) / (q : ℚ) - 1) := hw
      _ = (((p * (p ^ 2 + p * (q : ℤ) - (q : ℤ) ^ 2) : ℤ) : ℚ) /
            (q : ℚ) ^ 3) := by
            field_simp [hq0Q]
            ring

  obtain ⟨d, a, hd, hq_square, ha⟩ :=
    lowest_terms_valuation_package p q hq hpq w hclear_rat

  refine ⟨d, a, hd, hq_square, ha, ?_⟩
  exact int_gcd_eq_one_of_natAbs_square_eq hpq hq_square

end ScratchDenominator
```
