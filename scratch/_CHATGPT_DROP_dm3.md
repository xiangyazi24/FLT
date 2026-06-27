# Q1493 (dm3): helper lemmas for quartic descent

## Executive answer

For the first helper, your `nlinarith` proof is correct, except the theorem statement needs `s` quantified.

For the coprimality helper, use the same `IsRelPrime` / prime-divisor pattern as `UV_coprime`.  The proof is shorter here:

* a common prime divisor of `r - h` and `r + h` divides `2r` and `2h`;
* the `p = 2` case contradicts `r % 2 = 1` and `h % 2 = 0`;
* hence `p ∣ r` and `p ∣ h`;
* from `r^2 = h^2 + b^4`, get `p ∣ b^4`, hence `p ∣ b`;
* contradiction with `Int.gcd r b = 1`.

The second factorization lemma should indeed be just a wrapper around your project-local
`pos_fourth_of_coprime_mul_fourth` after you have `coprime_rh`.  I did not find that lemma by connector search in `xiangyazi24/FLT`, so I give the wrapper pattern below rather than pretending to know its exact argument order.

## Lean code

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace FLT.DM3

lemma two_dvd_of_emod_eq_zero {z : ℤ} (hz : z % 2 = 0) :
    (2 : ℤ) ∣ z := by
  exact Int.modEq_zero_iff_dvd.mp
    (by simpa [Int.ModEq, hz] : z ≡ 0 [ZMOD (2 : ℤ)])

lemma not_two_dvd_of_emod_eq_one {z : ℤ} (hz : z % 2 = 1) :
    ¬ (2 : ℤ) ∣ z := by
  intro h
  have h0 : z % 2 = 0 := by
    simpa [Int.ModEq] using
      (Int.modEq_zero_iff_dvd.mpr h : z ≡ 0 [ZMOD (2 : ℤ)])
  rw [hz] at h0
  norm_num at h0

/--
The algebraic identity after the first coprime factorization branch
`U = a^4`, `V = 5*b^4`.

This is pure algebra.  The variable `s` must be included in the binders. -/
theorem descent_identity {r a b s : ℤ}
    (hU : 2 * r ^ 2 + (a * b) ^ 2 - 2 * s = a ^ 4)
    (hV : 2 * r ^ 2 + (a * b) ^ 2 + 2 * s = 5 * b ^ 4) :
    4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
  nlinarith [hU, hV]

/--
Coprimality of `r-h` and `r+h` in the second factorization step.

Use this before applying the fourth-power factorization lemma to
`(r-h) * (r+h) = b^4`.
-/
theorem coprime_rh {r h b : ℤ} (hr_odd : r % 2 = 1) (hh_even : h % 2 = 0)
    (hcop_rb : Int.gcd r b = 1) (heq : r ^ 2 = h ^ 2 + b ^ 4) :
    Int.gcd (r - h) (r + h) = 1 := by
  classical

  let U : ℤ := r - h
  let V : ℤ := r + h
  change Int.gcd U V = 1

  have h2h : (2 : ℤ) ∣ h := two_dvd_of_emod_eq_zero hh_even

  have hcopI : IsCoprime r b := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd_def] using hcop_rb

  have hrel : IsRelPrime U V := by
    intro d hdU hdV
    by_contra hd_not_unit

    have hd_nat_ne_one : d.natAbs ≠ 1 := by
      intro hdabs
      exact hd_not_unit (Int.isUnit_iff_natAbs_eq.mpr hdabs)

    obtain ⟨p, hp, hpd_nat⟩ := Nat.exists_prime_and_dvd hd_nat_ne_one
    have hpd : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd_nat
    have hpU : (p : ℤ) ∣ U := hpd.trans hdU
    have hpV : (p : ℤ) ∣ V := hpd.trans hdV

    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst p
      have h2r : (2 : ℤ) ∣ r := by
        have h2Uh : (2 : ℤ) ∣ U + h := dvd_add hpU h2h
        convert h2Uh using 1
        ring_nf [U]
      exact (not_two_dvd_of_emod_eq_one hr_odd) h2r

    have hpr : (p : ℤ) ∣ r := by
      have hp2r0 : (p : ℤ) ∣ U + V := dvd_add hpU hpV
      have hp2r : (p : ℤ) ∣ 2 * r := by
        convert hp2r0 using 1
        ring_nf [U, V]
      rcases Int.Prime.dvd_mul' hp hp2r with hp_dvd_two | hpr
      · have hp_dvd_two_nat : p ∣ (2 : ℕ) := by
          exact_mod_cast hp_dvd_two
        have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_two_nat
        exact (hp_ne_two (le_antisymm hple2 hp.two_le)).elim
      · exact hpr

    have hph : (p : ℤ) ∣ h := by
      have hp2h0 : (p : ℤ) ∣ V - U := dvd_sub hpV hpU
      have hp2h : (p : ℤ) ∣ 2 * h := by
        convert hp2h0 using 1
        ring_nf [U, V]
      rcases Int.Prime.dvd_mul' hp hp2h with hp_dvd_two | hph
      · have hp_dvd_two_nat : p ∣ (2 : ℕ) := by
          exact_mod_cast hp_dvd_two
        have hple2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd_two_nat
        exact (hp_ne_two (le_antisymm hple2 hp.two_le)).elim
      · exact hph

    have hpb4 : (p : ℤ) ∣ b ^ 4 := by
      have hpr2 : (p : ℤ) ∣ r ^ 2 := pow_dvd_pow hpr 2
      have hph2 : (p : ℤ) ∣ h ^ 2 := pow_dvd_pow hph 2
      have hdiff_dvd : (p : ℤ) ∣ r ^ 2 - h ^ 2 := dvd_sub hpr2 hph2
      have hdiff : r ^ 2 - h ^ 2 = b ^ 4 := by
        nlinarith [heq]
      simpa [hdiff] using hdiff_dvd

    have hpb : (p : ℤ) ∣ b := Int.Prime.dvd_pow' hp hpb4
    have hunitp : IsUnit (p : ℤ) := hcopI.isUnit_of_dvd' hpr hpb
    exact (Nat.prime_iff_prime_int.mp hp).not_unit hunitp

  have hcopUV : IsCoprime U V := isRelPrime_iff_isCoprime.mp hrel
  have hcopUV_nat : Nat.Coprime U.natAbs V.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hcopUV
  simpa [Int.gcd_def, Nat.coprime_iff_gcd_eq_one] using hcopUV_nat

end FLT.DM3
```

## Second factorization wrapper

Once your project-local lemma is imported, the wrapper should be this shape:

```lean
/-- Expected project-local theorem shape.  Do not duplicate this if it already exists. -/
-- theorem pos_fourth_of_coprime_mul_fourth
--     {x y z : ℤ} (hx : 0 < x) (hy : 0 < y)
--     (hcop : Int.gcd x y = 1) (hmul : x * y = z ^ 4) :
--     ∃ α β : ℤ,
--       0 < α ∧ 0 < β ∧ x = α ^ 4 ∧ y = β ^ 4 ∧ z = α * β := ...

theorem rh_fourth_factorization
    {r h b : ℤ}
    (hpos_left : 0 < r - h) (hpos_right : 0 < r + h)
    (hr_odd : r % 2 = 1) (hh_even : h % 2 = 0)
    (hcop_rb : Int.gcd r b = 1)
    (heq_sq : r ^ 2 = h ^ 2 + b ^ 4)
    (hmul : (r - h) * (r + h) = b ^ 4) :
    ∃ α β : ℤ,
      0 < α ∧ 0 < β ∧
      r - h = α ^ 4 ∧ r + h = β ^ 4 ∧ b = α * β := by
  have hcop : Int.gcd (r - h) (r + h) = 1 :=
    coprime_rh hr_odd hh_even hcop_rb heq_sq
  exact pos_fourth_of_coprime_mul_fourth
    hpos_left hpos_right hcop hmul
```

If your `pos_fourth_of_coprime_mul_fourth` uses `Nat` variables or returns `|b| = αβ` instead of `b = αβ`, keep `coprime_rh` unchanged and only adjust the wrapper’s casts/sign conclusion.  The gcd helper is independent of the positivity hypotheses.

## If `nlinarith` does not close `descent_identity`

It should close directly.  If local normalization is weaker in your file context, use:

```lean
  ring_nf at hU hV ⊢
  nlinarith [hU, hV]
```

The identity is exactly the sum of the two factor equations followed by expanding `(a^2-b^2)^2`.
