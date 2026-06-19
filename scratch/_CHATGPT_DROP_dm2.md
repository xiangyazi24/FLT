# Lean drop: `u.den = 1` for rational points on `w² = u³ + u² - u`

Below is the drop-in Lean proof structure.  The only proof hole is the deliberately isolated denominator-clearing / prime-valuation package.  The final theorem itself uses no descent beyond the already-existing `no_denominator_quartic` obstruction.

```lean
import Mathlib
import DenominatorQuartic

namespace ScratchDenominator

/--
Adapter for the theorem exported by `DenominatorQuartic.lean`.

This is intentionally a tiny wrapper: if the local theorem has the same
mathematical statement but a different argument order, this is the only line
that should need editing.
-/
lemma denominator_quartic_lt_two
    (d s t : ℕ)
    (hquartic : t ^ 2 = s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4) :
    d < 2 := by
  exact no_denominator_quartic d s t hquartic

/--
The isolated clearing/valuation step.

Mathematical content packaged here:

* Write `u = n / q` and `w = a / b` in lowest terms, where
  `n = u.num`, `q = u.den`, `a = w.num`, `b = w.den`.
* Clearing denominators in
  `w² = u³ + u² - u` gives
  `a² * q³ = b² * (n * (n² + n*q - q²))`.
* For every prime `p ∣ q`, the integer
  `N = n * (n² + n*q - q²)` is not divisible by `p`, because
  `N ≡ n³ [ZMOD p]` and `Nat.Coprime n.natAbs q`.
* Comparing `p`-adic valuations forces all exponents in `q` to be even.
  Hence `q = d²`; then the same valuation comparison gives `b = d³`.
* Consequently
  `a² = n * (n² + n*d² - d⁴)`.
* Splitting the coprime square product gives the denominator quartic needed
  by `no_denominator_quartic`.

This lemma is the only place where the Rat/Int/Nat normalization API and
prime-valuation bookkeeping should be painful.
-/
lemma clearing_to_denominator_quartic
    (u w : ℚ)
    (hcurve : w ^ 2 = u ^ 3 + u ^ 2 - u)
    (hu : u ≠ 0)
    (hden : 2 ≤ u.den) :
    ∃ d s t : ℕ,
      2 ≤ d ∧
      u.den = d ^ 2 ∧
      t ^ 2 = s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 := by
  sorry

/--
Rational points on `w² = u³ + u² - u`, with `u ≠ 0`, have integral
`u`-coordinate.
-/
theorem rat_curve_den_eq_one
    (u w : ℚ)
    (hcurve : w ^ 2 = u ^ 3 + u ^ 2 - u)
    (hu : u ≠ 0) :
    u.den = 1 := by
  classical
  by_contra hden_ne_one
  have hden_pos : 0 < u.den := Nat.pos_of_ne_zero u.den_nz
  have hden_ge_two : 2 ≤ u.den := by
    omega

  obtain ⟨d, s, t, hd_ge_two, hden_sq, hquartic⟩ :=
    clearing_to_denominator_quartic u w hcurve hu hden_ge_two

  have hd_lt_two : d < 2 :=
    denominator_quartic_lt_two d s t hquartic

  omega

end ScratchDenominator
```

If `DenominatorQuartic.lean` states the obstruction in the `False` form rather than the `d < 2` form, replace only the adapter by:

```lean
lemma denominator_quartic_lt_two
    (d s t : ℕ)
    (hquartic : t ^ 2 = s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4) :
    d < 2 := by
  by_contra hd_not_lt
  have hd_ge_two : 2 ≤ d := by omega
  exact False.elim (no_denominator_quartic d s t hd_ge_two hquartic)
```
