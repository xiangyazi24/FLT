# Q1449 (dm1): `V_pos` and the clean `UV_coprime` core

The key correction is: do **not** try to prove `d ∣ B` directly from `d ∣ s` and `d ∣ 2*r^2+B^2`.  The clean seam is instead:

```text
A := 2*r^2 + B^2
U := A - 2*s
V := A + 2*s
```

A common divisor of `U,V` divides `U+V = 2*A`.  Since `U` is odd, that common divisor is coprime to `2`, hence it divides `A`.  It also divides `U*V = 5*B^4`.  Therefore it is enough to have the separate arithmetic lemma

```lean
Int.gcd (2 * r ^ 2 + B ^ 2) (5 * B ^ 4) = 1
```

which is where the `gcd(r,B)=1` plus the mod-`5` nonresidue check belongs.  This avoids the bad `d ∣ B` shortcut and keeps `UV_coprime` small.

Here is the Lean block I would drop in.  The theorem named `UV_coprime` is the reusable core: it assumes the exact `A`-coprimality seam, then proves the required `Int.gcd U V = 1`.

```lean
import Mathlib

namespace DM1

abbrev A (r B : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2
abbrev U (r B s : ℤ) : ℤ := A r B - 2 * s
abbrev V (r B s : ℤ) : ℤ := A r B + 2 * s

lemma UV_eq_5B4_of_quartic {r B s : ℤ}
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    U r B s * V r B s = 5 * B ^ 4 := by
  calc
    U r B s * V r B s
        = (2 * r ^ 2 + B ^ 2) ^ 2 - (2 * s) ^ 2 := by
          dsimp [U, V, A]
          ring
    _ = 5 * B ^ 4 := by
          nlinarith [heq]

/-- Positivity of the upper factor, using only the factor-product identity. -/
lemma V_pos_of_UV {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hUV : U r B s * V r B s = 5 * B ^ 4) :
    0 < V r B s := by
  by_contra hV
  push_neg at hV
  have hU_nonneg : 0 ≤ U r B s := by
    dsimp [U, V, A] at hV ⊢
    nlinarith [sq_nonneg r, sq_nonneg B]
  have hprod_nonpos : U r B s * V r B s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hU_nonneg hV
  have hprod_pos : 0 < U r B s * V r B s := by
    rw [hUV]
    have hB4 : 0 < B ^ 4 := pow_pos hB 4
    nlinarith
  nlinarith

/-- Positivity of the upper factor directly from the quartic equation. -/
theorem V_pos {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    0 < V r B s := by
  exact V_pos_of_UV (r := r) (B := B) (s := s) hr hB
    (UV_eq_5B4_of_quartic (r := r) (B := B) (s := s) heq)

/-- If an integer divides an odd integer, then it is coprime to `2`. -/
lemma gcd_two_eq_one_of_dvd_odd {e n : ℤ}
    (hen : e ∣ n) (hnodd : Odd n) :
    Int.gcd e 2 = 1 := by
  rcases hen with ⟨q, hq⟩
  rcases hnodd with ⟨k, hk⟩
  rw [hq] at hk
  have hbez : (1 : ℤ) = e * q + 2 * (-k) := by
    nlinarith
  exact Nat.dvd_one.mp
    ((Int.gcd_dvd_iff (a := e) (b := 2) (n := 1)).mpr ⟨q, -k, hbez⟩)

/-- A common divisor of `U,V` divides `A`, once `U` is odd. -/
lemma common_dvd_A_of_U_odd {r B s e : ℤ}
    (heU : e ∣ U r B s) (heV : e ∣ V r B s)
    (hUodd : Odd (U r B s)) :
    e ∣ A r B := by
  have hsum : e ∣ U r B s + V r B s := dvd_add heU heV
  have hsum_eq : U r B s + V r B s = 2 * A r B := by
    dsimp [U, V, A]
    ring
  have he2A : e ∣ 2 * A r B := by
    rwa [hsum_eq] at hsum
  exact Int.dvd_of_dvd_mul_right_of_gcd_one he2A
    (gcd_two_eq_one_of_dvd_odd heU hUodd)

/--
Core coprimality lemma for the quartic factors.

The remaining arithmetic seam is `hAcop`.  In the full descent file, prove it separately from
`Int.gcd r B = 1`, `B` odd, and the mod-`5` fact that
`2*x^2 + y^2 ≠ 0` in `ZMod 5` for nonzero square classes.
-/
theorem UV_coprime_of_A_coprime {r B s : ℤ}
    (hUodd : Odd (U r B s))
    (hUV : U r B s * V r B s = 5 * B ^ 4)
    (hAcop : Int.gcd (A r B) (5 * B ^ 4) = 1) :
    Int.gcd (U r B s) (V r B s) = 1 := by
  have hmain : (1 : ℤ) = (Int.gcd (U r B s) (V r B s) : ℤ) := by
    refine Int.gcd_greatest
      (a := U r B s) (b := V r B s) (d := 1)
      (by norm_num) (one_dvd _) (one_dvd _) ?_
    intro e heU heV
    have heA : e ∣ A r B :=
      common_dvd_A_of_U_odd
        (r := r) (B := B) (s := s) (e := e) heU heV hUodd
    have heProd : e ∣ U r B s * V r B s := dvd_mul_of_dvd_left heU _
    have he5B4 : e ∣ 5 * B ^ 4 := by
      rwa [hUV] at heProd
    have hegcd : e ∣ (Int.gcd (A r B) (5 * B ^ 4) : ℤ) :=
      Int.dvd_coe_gcd heA he5B4
    simpa [hAcop] using hegcd
  exact_mod_cast hmain.symm

/-- Same core lemma, if oddness has already been stored as `% 2 = 1`. -/
theorem UV_coprime {r B s : ℤ}
    (hUodd : U r B s % 2 = 1)
    (hUV : U r B s * V r B s = 5 * B ^ 4)
    (hAcop : Int.gcd (A r B) (5 * B ^ 4) = 1) :
    Int.gcd (U r B s) (V r B s) = 1 := by
  exact UV_coprime_of_A_coprime
    (r := r) (B := B) (s := s)
    (Int.odd_iff.mpr hUodd) hUV hAcop

end DM1
```

The `hAcop` seam should be proved as its own lemma, not inside `UV_coprime`.  Mathematically it is:

```text
gcd(2*r^2+B^2, B) = 1     from gcd(r,B)=1 and B odd
gcd(2*r^2+B^2, 5) = 1     from the square classes mod 5
therefore gcd(2*r^2+B^2, 5*B^4) = 1.
```

That is the place to use `ZMod 5` or a finite `% 5` case split.  Once that lemma is available, the factor gcd proof above is the small stable piece.