# Q2633 remaining `EulerSquarePairDescent` helper layer

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.

Target namespace from earlier work:

```lean
namespace MazurProof.RationalPointsN12.EulerSquarePair
```

The snippets below are designed to be pasted near the descent construction.  They do not depend on the exact return tuple order of `signed_even_odd_params_same_orientation`; instead, they give a core bridge from the existing Nat refinement output to the Int equations required by `refinement_equation_of_same_orientation`, plus the coprime/parity/descent lemmas needed afterwards.

Add the import for the square-balance theorem:

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12EulerAux
```

## A. Nat refinement output to Int refined factors

Use `q2633_natAbs_mul_eq_of_pos` to feed the Nat refinement theorem, then use `q2633_halve_refined_nat_common_factor_to_int` after `two_coprime_factorizations_refine_nat` returns the common Nat factor.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12EulerAux

namespace MazurProof.RationalPointsN12.EulerSquarePair

@[simp] private lemma q2633_natAbs_cast_of_pos {x : ℤ} (hx : 0 < x) :
    (x.natAbs : ℤ) = x := by
  rw [Nat.cast_natAbs]
  exact abs_of_pos hx

private lemma q2633_natAbs_pos_of_pos {x : ℤ} (hx : 0 < x) :
    0 < x.natAbs := by
  have hx' : (0 : ℤ) < (x.natAbs : ℤ) := by
    rw [q2633_natAbs_cast_of_pos hx]
    exact hx
  exact_mod_cast hx'

private lemma q2633_natAbs_mul_eq_of_pos
    {U V Up Vp : ℤ}
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hUppos : 0 < Up) (hVppos : 0 < Vp)
    (hEq : U * V = Up * Vp) :
    U.natAbs * V.natAbs = Up.natAbs * Vp.natAbs := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul, Nat.cast_mul]
  rw [q2633_natAbs_cast_of_pos hUpos, q2633_natAbs_cast_of_pos hVpos,
    q2633_natAbs_cast_of_pos hUppos, q2633_natAbs_cast_of_pos hVppos]
  exact hEq

private lemma q2633_nat_odd_left_of_odd_mul {a b : ℕ}
    (h : Odd (a * b)) : Odd a := by
  rw [← not_even_iff_odd] at h ⊢
  intro ha
  exact h (ha.mul_right b)

private lemma q2633_nat_odd_right_of_odd_mul {a b : ℕ}
    (h : Odd (a * b)) : Odd b := by
  rw [mul_comm] at h
  exact q2633_nat_odd_left_of_odd_mul h

private lemma q2633_nat_even_left_of_even_mul_odd_right {a b : ℕ}
    (hab : Even (a * b)) (hb : Odd b) : Even a := by
  by_contra haEven
  have haOdd : Odd a := (not_even_iff_odd).mp haEven
  have hOdd : Odd (a * b) := haOdd.mul hb
  have hNotEven : ¬ Even (a * b) := (not_even_iff_odd).mpr hOdd
  exact hNotEven hab

/--
Bridge from the Nat common refinement to the Int factorization needed by
`refinement_equation_of_same_orientation`.

Here `r` is the common Nat factor returned by
`two_coprime_factorizations_refine_nat`; the theorem proves `r` is even because
`U = r*b` is even and `b` is odd, then renames `r = 2*a`.

The two Nat coprimality inputs are the only pairwise-coprime facts this bridge
uses directly:
* `hrd_coprime : Nat.Coprime r d`, to get `IsCoprime a d` after halving `r`;
* `hbc_coprime : Nat.Coprime b c`, to get `IsCoprime b c` over `Int`.
-/
private theorem q2633_halve_refined_nat_common_factor_to_int
    {U V Up Vp : ℤ} {r b c d : ℕ}
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hUppos : 0 < Up) (hVppos : 0 < Vp)
    (hrpos : 0 < r) (hbpos : 0 < b) (hcpos : 0 < c) (hdpos : 0 < d)
    (hU_nat : U.natAbs = r * b)
    (hV_nat : V.natAbs = c * d)
    (hUp_nat : Up.natAbs = r * c)
    (hVp_nat : Vp.natAbs = b * d)
    (hUeven : Even U) (hVodd : Odd V)
    (hUpeven : Even Up) (hVpodd : Odd Vp)
    (hrd_coprime : Nat.Coprime r d)
    (hbc_coprime : Nat.Coprime b c) :
    ∃ a bI cI dI : ℤ,
      0 < a ∧ 0 < bI ∧ 0 < cI ∧ 0 < dI ∧
      Odd dI ∧ IsCoprime a dI ∧ IsCoprime bI cI ∧
      U = 2 * a * bI ∧ V = cI * dI ∧
      Up = 2 * a * cI ∧ Vp = bI * dI := by
  have hVnatOdd : Odd V.natAbs := (Int.natAbs_odd (n := V)).mpr hVodd
  have hVpnatOdd : Odd Vp.natAbs := (Int.natAbs_odd (n := Vp)).mpr hVpodd
  have hcdOdd : Odd (c * d) := by
    simpa [hV_nat] using hVnatOdd
  have hbdOdd : Odd (b * d) := by
    simpa [hVp_nat] using hVpnatOdd
  have hdOddNat : Odd d := q2633_nat_odd_right_of_odd_mul hcdOdd
  have hbOddNat : Odd b := q2633_nat_odd_left_of_odd_mul hbdOdd
  have hUnatEven : Even U.natAbs := (Int.natAbs_even (n := U)).mpr hUeven
  have hrbEven : Even (r * b) := by
    simpa [hU_nat] using hUnatEven
  have hrEven : Even r :=
    q2633_nat_even_left_of_even_mul_odd_right hrbEven hbOddNat
  rcases (even_iff_two_dvd.mp hrEven) with ⟨a, hr_eq⟩
  have hapos : 0 < a := by omega
  have hU_cast : U = (r : ℤ) * (b : ℤ) := by
    calc
      U = (U.natAbs : ℤ) := (q2633_natAbs_cast_of_pos hUpos).symm
      _ = ((r * b : ℕ) : ℤ) := by exact_mod_cast hU_nat
      _ = (r : ℤ) * (b : ℤ) := by norm_cast
  have hV_cast : V = (c : ℤ) * (d : ℤ) := by
    calc
      V = (V.natAbs : ℤ) := (q2633_natAbs_cast_of_pos hVpos).symm
      _ = ((c * d : ℕ) : ℤ) := by exact_mod_cast hV_nat
      _ = (c : ℤ) * (d : ℤ) := by norm_cast
  have hUp_cast : Up = (r : ℤ) * (c : ℤ) := by
    calc
      Up = (Up.natAbs : ℤ) := (q2633_natAbs_cast_of_pos hUppos).symm
      _ = ((r * c : ℕ) : ℤ) := by exact_mod_cast hUp_nat
      _ = (r : ℤ) * (c : ℤ) := by norm_cast
  have hVp_cast : Vp = (b : ℤ) * (d : ℤ) := by
    calc
      Vp = (Vp.natAbs : ℤ) := (q2633_natAbs_cast_of_pos hVppos).symm
      _ = ((b * d : ℕ) : ℤ) := by exact_mod_cast hVp_nat
      _ = (b : ℤ) * (d : ℤ) := by norm_cast
  have hrInt : (r : ℤ) = 2 * (a : ℤ) := by exact_mod_cast hr_eq
  have had : IsCoprime (a : ℤ) (d : ℤ) := by
    have hrd : IsCoprime (r : ℤ) (d : ℤ) := Nat.Coprime.isCoprime hrd_coprime
    apply hrd.of_isCoprime_of_dvd_left
    refine ⟨(2 : ℤ), ?_⟩
    rw [hrInt]
    ring
  have hbc : IsCoprime (b : ℤ) (c : ℤ) := Nat.Coprime.isCoprime hbc_coprime
  have haIpos : 0 < (a : ℤ) := by exact_mod_cast hapos
  have hbIpos : 0 < (b : ℤ) := by exact_mod_cast hbpos
  have hcIpos : 0 < (c : ℤ) := by exact_mod_cast hcpos
  have hdIpos : 0 < (d : ℤ) := by exact_mod_cast hdpos
  have hdOddInt : Odd (d : ℤ) := (Int.odd_coe_nat d).mpr hdOddNat
  refine ⟨a, b, c, d, haIpos, hbIpos, hcIpos, hdIpos, hdOddInt, had, hbc, ?_, hV_cast, ?_, hVp_cast⟩
  · rw [hU_cast, hrInt]
    ring
  · rw [hUp_cast, hrInt]
    ring

/-!
Application skeleton after
`obtain ⟨U,V,Up,Vp,...⟩ := signed_even_odd_params_same_orientation E`:

```lean
have hEqNat : U.natAbs * V.natAbs = Up.natAbs * Vp.natAbs :=
  q2633_natAbs_mul_eq_of_pos hUpos hVpos hUppos hVppos hAeq
have hUVNat : Nat.Coprime U.natAbs V.natAbs :=
  Int.isCoprime_iff_nat_coprime.mp hUVcop
have hUpVpNat : Nat.Coprime Up.natAbs Vp.natAbs :=
  Int.isCoprime_iff_nat_coprime.mp hUpVpcop
have hUnpos : 0 < U.natAbs := q2633_natAbs_pos_of_pos hUpos
have hVnpos : 0 < V.natAbs := q2633_natAbs_pos_of_pos hVpos
have hUpnpos : 0 < Up.natAbs := q2633_natAbs_pos_of_pos hUppos
have hVpnpos : 0 < Vp.natAbs := q2633_natAbs_pos_of_pos hVppos
obtain ⟨r,b,c,d,hrpos,hbpos,hcpos,hdpos,
  hU_nat,hV_nat,hUp_nat,hVp_nat,hPairwise⟩ :=
  two_coprime_factorizations_refine_nat
    hUnpos hVnpos hEqNat hUVNat hUpVpNat
-- destruct `hPairwise` according to the local theorem's exact tuple;
-- the bridge below only needs `Nat.Coprime r d` and `Nat.Coprime b c`.
obtain ⟨a,bI,cI,dI,ha,hb,hc,hd,hdOdd,had,hbc,hU,hV,hUp,hVp⟩ :=
  q2633_halve_refined_nat_common_factor_to_int
    hUpos hVpos hUppos hVppos hrpos hbpos hcpos hdpos
    hU_nat hV_nat hUp_nat hVp_nat hUeven hVodd hUpeven hVpodd
    hrd_coprime hbc_coprime
have hbalance := refinement_equation_of_same_orientation hU hV hUp hVp hsame
```
-/
```

## B. Int coprimality for balance extraction

The Nat-to-Int bridge above already returns the two Int facts that `square_factor_balance_int` needs on the square factors:

```lean
had : IsCoprime a d
hbc : IsCoprime b c
```

For the cofactor coprimality, reuse your existing `euler_cofactor_coprime`.

```lean
namespace MazurProof.RationalPointsN12.EulerSquarePair

private lemma q2633_euler_cofactor_coprime_int {a d : ℤ}
    (hdOdd : Odd d) (had : IsCoprime a d) :
    IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2) := by
  simpa using euler_cofactor_coprime hdOdd had

/-!
Expected balance call, modulo the exact argument order of
`N12EulerAux.square_factor_balance_int`:

```lean
have hcof : IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2) :=
  q2633_euler_cofactor_coprime_int hdOdd had
obtain ⟨hCnew, hBnew⟩ :=
  square_factor_balance_int hb hc hbc hcof hbalance
-- expected result orientation:
-- hCnew : 4 * a ^ 2 + d ^ 2 = c ^ 2
-- hBnew : 16 * a ^ 2 + d ^ 2 = b ^ 2
```

If the existing theorem's argument order is inconvenient, the precise wrapper to
ask for next is:

```lean
theorem square_factor_balance_for_descent
    {a b c d : ℤ}
    (hbpos : 0 < b) (hcpos : 0 < c)
    (hbc : IsCoprime b c)
    (hcof : IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2))
    (hbalance : b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2)) :
    4 * a ^ 2 + d ^ 2 = c ^ 2 ∧
      16 * a ^ 2 + d ^ 2 = b ^ 2
```
-/

end MazurProof.RationalPointsN12.EulerSquarePair
```

## C. Positivity and parity for the new Euler pair

The bridge in section A gives:

```lean
ha : 0 < a
hb : 0 < b
hc : 0 < c
hd : 0 < d
hdOdd : Odd d
had : IsCoprime a d
hbc : IsCoprime b c
```

The missing field is `Even a`.  Prove it after square extraction from
`4*a^2 + d^2 = c^2`.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12.EulerSquarePair

private theorem q2633_sq_ne_five_zmod_eight (z : ZMod 8) :
    z * z ≠ 5 := by
  change Fin 8 at z
  fin_cases z <;> decide

private lemma q2633_odd_sq_zmod_eight {z : ℤ} (hz : Odd z) :
    ((z : ZMod 8) * (z : ZMod 8)) = 1 := by
  rcases hz with ⟨k, rfl⟩
  have htwo : (2 : ℤ) ∣ k * (k + 1) := Int.two_dvd_mul_add_one k
  rcases htwo with ⟨t, ht⟩
  have hmain : (2 * k + 1) * (2 * k + 1) = 8 * t + 1 := by
    calc
      (2 * k + 1) * (2 * k + 1) = 4 * (k * (k + 1)) + 1 := by ring
      _ = 8 * t + 1 := by rw [ht]; ring
  calc
    (((2 * k + 1 : ℤ) : ZMod 8) * ((2 * k + 1 : ℤ) : ZMod 8))
        = ((8 * t + 1 : ℤ) : ZMod 8) := by exact_mod_cast hmain
    _ = 1 := by norm_num

/--
If `d` is odd and `C^2 = 4*a^2 + d^2`, then `a` is even.  This is the
mod-8 obstruction: if `a` were odd, the RHS would be `5 mod 8`.
-/
private lemma q2633_even_a_of_square_cofactor {a d C : ℤ}
    (hdOdd : Odd d)
    (hC : C ^ 2 = 4 * a ^ 2 + d ^ 2) :
    Even a := by
  by_contra haEven
  have haOdd : Odd a := Int.not_even_iff_odd.mp haEven
  have ha1 : ((a : ZMod 8) ^ 2) = 1 := by
    simpa [pow_two] using q2633_odd_sq_zmod_eight haOdd
  have hd1 : ((d : ZMod 8) ^ 2) = 1 := by
    simpa [pow_two] using q2633_odd_sq_zmod_eight hdOdd
  have hCz : ((C : ZMod 8) ^ 2) = 4 * ((a : ZMod 8) ^ 2) + ((d : ZMod 8) ^ 2) := by
    exact_mod_cast hC
  have hCfive : ((C : ZMod 8) * (C : ZMod 8)) = 5 := by
    calc
      ((C : ZMod 8) * (C : ZMod 8)) = ((C : ZMod 8) ^ 2) := by ring
      _ = 4 * ((a : ZMod 8) ^ 2) + ((d : ZMod 8) ^ 2) := hCz
      _ = 5 := by rw [ha1, hd1]; norm_num
  exact q2633_sq_ne_five_zmod_eight (C : ZMod 8) hCfive

/-!
Usage after square balance:

```lean
have haEven : Even a := q2633_even_a_of_square_cofactor hdOdd hCnew.symm
-- if your balance theorem returns `c ^ 2 = 4*a^2+d^2`, use it directly:
-- have haEven : Even a := q2633_even_a_of_square_cofactor hdOdd hCnew
```
-/

end MazurProof.RationalPointsN12.EulerSquarePair
```

## D. Strict descent

This proves the stronger local target `a*d < E.A`.  The only needed equation is the refined factorization of `E.A`.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12.EulerSquarePair

private lemma q2633_ad_lt_A_of_refined_A
    {A a b c d : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : A = (2 * a * b) * (c * d)) :
    a * d < A := by
  have hadpos : 0 < a * d := mul_pos ha hd
  have hb1 : (1 : ℤ) ≤ b := by omega
  have hc1 : (1 : ℤ) ≤ c := by omega
  have hbc1 : (1 : ℤ) ≤ b * c := by
    exact mul_le_mul hb1 hc1 (by norm_num) (by omega)
  have hfac : (1 : ℤ) < 2 * b * c := by nlinarith
  calc
    a * d = 1 * (a * d) := by ring
    _ < (2 * b * c) * (a * d) := mul_lt_mul_of_pos_right hfac hadpos
    _ = (2 * a * b) * (c * d) := by ring
    _ = A := hA.symm

private lemma q2633_ad_lt_A_mul_D_of_refined_A
    {A D a b c d : ℤ}
    (hApos : 0 < A) (hDpos : 0 < D)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hA : A = (2 * a * b) * (c * d)) :
    a * d < A * D := by
  have hltA : a * d < A := q2633_ad_lt_A_of_refined_A ha hb hc hd hA
  have hD1 : (1 : ℤ) ≤ D := by omega
  have hAle : A ≤ A * D := by nlinarith
  exact lt_of_lt_of_le hltA hAle

/-!
Usage:

```lean
have hA_refined : E.A = (2 * a * b) * (c * d) := by
  rw [hA_from_signed, hU, hV]
  ring
have hdescA : a * d < E.A :=
  q2633_ad_lt_A_of_refined_A ha hb hc hd hA_refined
have hdescAD : a * d < E.A * E.D :=
  q2633_ad_lt_A_mul_D_of_refined_A E.hApos E.hDpos ha hb hc hd hA_refined
```
-/

end MazurProof.RationalPointsN12.EulerSquarePair
```

## API names referenced

* Nat-to-Int cast equality from positivity:
  `Nat.cast_natAbs` plus `abs_of_pos`; packaged above as `q2633_natAbs_cast_of_pos`.
* NatAbs parity transfer:
  `Int.natAbs_even : Even n.natAbs ↔ Even n` and `Int.natAbs_odd : Odd n.natAbs ↔ Odd n`.
* Nat-to-Int odd transfer:
  `Int.odd_coe_nat n : Odd (n : ℤ) ↔ Odd n`.
* Int/Nat coprime transfer:
  `Int.isCoprime_iff_nat_coprime : IsCoprime a b ↔ Nat.Coprime a.natAbs b.natAbs` and `Nat.Coprime.isCoprime`.
* Even division by `2` over Nat:
  `even_iff_two_dvd.mp hEven`, then `rcases ... with ⟨a, h⟩`; the witness equation is `h : r = 2 * a`.
* Divisibility/coprime monotonicity over `Int`:
  `IsCoprime.of_isCoprime_of_dvd_left`.
* Inequality casts:
  `exact_mod_cast`, `Nat.cast_injective (R := ℤ)`, and `omega` for integer discreteness such as `0 < b : ℤ ⟹ 1 ≤ b`.
