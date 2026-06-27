# Q1398/Q1399/Q1401/Q1403/Q1404 (dm1): quartic-plus descent algebra bundle

This bundles the five requested quartic-descent substeps.

What is mechanical and should be kept as small lemmas:

* `4*r^2 = a^4 - 2*a^2*b^2 + 5*b^4` from the `U,V` split and `a*b=B`.
* `(a^2-b^2)^2 + 4*b^4` algebra.
* `h=(a^2-b^2)/2` and `h^2+b^4=r^2`.
* `gcd(h,b^2)=1` from `gcd(a,b)=1` and `2*h=a^2-b^2`.
* `U,V>0` from product-positive plus sum-positive.
* `U,V` odd from `r,B` odd.
* non-baseness of the new solution `(v,u,a)` from old non-baseness.

What is **not** honestly completed by the proposed modular sketches:

* `gcd(U,V)=1` is a real local number-theory lemma; the clean proof uses common-prime divisors and a final mod-5 square-residue contradiction.
* `quartic_plus_both_odd` still has the known gap in the `r` odd, `4 ∣ B` subcase.  The mod-16 argument only rules out `v₂(B)=1`, not `4 ∣ B`.

## Shared definitions

```lean
import Mathlib

namespace DM1

abbrev U (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
abbrev V (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

def BaseZ (r B : ℤ) : Prop := r = 1 ∧ B = 1

end DM1
```

## Q1398: algebra after `U=a^4`, `V=5*b^4`

```lean
import Mathlib

namespace DM1

/-- From `U+V = 2*(2*r^2+B^2)` and the split `U=a^4`, `V=5*b^4`. -/
lemma four_r_sq_from_split
    {a b r B : ℤ}
    (habB : a * b = B)
    (hsum : a ^ 4 + 5 * b ^ 4 = 4 * r ^ 2 + 2 * B ^ 2) :
    4 * r ^ 2 = a ^ 4 - 2 * a ^ 2 * b ^ 2 + 5 * b ^ 4 := by
  calc
    4 * r ^ 2 = a ^ 4 + 5 * b ^ 4 - 2 * B ^ 2 := by
      nlinarith
    _ = a ^ 4 - 2 * a ^ 2 * b ^ 2 + 5 * b ^ 4 := by
      rw [← habB]
      ring

lemma quartic_split_identity (a b : ℤ) :
    a ^ 4 - 2 * a ^ 2 * b ^ 2 + 5 * b ^ 4 =
      (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4 := by
  ring

/-- If `a,b` are odd, then `a^2-b^2` is even. -/
lemma two_dvd_sq_sub_sq_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    (2 : ℤ) ∣ a ^ 2 - b ^ 2 := by
  rcases ha with ⟨m, hm⟩
  rcases hb with ⟨n, hn⟩
  refine ⟨2 * m ^ 2 + 2 * m - (2 * n ^ 2 + 2 * n), ?_⟩
  rw [hm, hn]
  ring

/-- The Pythagorean equation after defining `h=(a^2-b^2)/2`. -/
lemma h_sq_add_b4_eq_r_sq
    {a b h r : ℤ}
    (hhalf : 2 * h = a ^ 2 - b ^ 2)
    (h4r : 4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4) :
    h ^ 2 + b ^ 4 = r ^ 2 := by
  have hsq : (a ^ 2 - b ^ 2) ^ 2 = 4 * h ^ 2 := by
    calc
      (a ^ 2 - b ^ 2) ^ 2 = (2 * h) ^ 2 := by rw [← hhalf]
      _ = 4 * h ^ 2 := by ring
  nlinarith

/-- From `gcd(a,b)=1` and `2*h=a^2-b^2`, get `gcd(h,b^2)=1`. -/
lemma gcd_h_bsq_eq_one
    {a b h : ℤ}
    (hgcd : Int.gcd a b = 1)
    (hhalf : 2 * h = a ^ 2 - b ^ 2) :
    Int.gcd h (b ^ 2) = 1 := by
  have hab : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr hgcd

  have ha2b : IsCoprime (a ^ 2) b := by
    simpa [pow_two] using (hab.mul_left hab)

  have ha2_eq : a ^ 2 = 2 * h + b * b := by
    rw [← hhalf]
    ring

  have htmp : IsCoprime (2 * h + b * b) b := by
    simpa [ha2_eq] using ha2b

  have h2h_b : IsCoprime (2 * h) b := by
    exact htmp.of_add_mul_left_left

  have hh_b : IsCoprime h b := by
    exact h2h_b.of_mul_left_right

  have hh_b2 : IsCoprime h (b ^ 2) := by
    simpa [pow_two] using (hh_b.mul_right hh_b)

  exact Int.isCoprime_iff_gcd_eq_one.mp hh_b2

end DM1
```

## Q1399/Q1401: `U,V` positivity, oddness, and the exact gcd gap

```lean
import Mathlib

namespace DM1

abbrev U (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
abbrev V (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

lemma UV_mul_eq_five_mul_B4 {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    U r B s * V r B s = 5 * B ^ 4 := by
  calc
    U r B s * V r B s = (2 * r ^ 2 + B ^ 2) ^ 2 - (2 * s) ^ 2 := by
      dsimp [U, V]
      ring
    _ = 5 * B ^ 4 := by
      rw [hs]
      ring

lemma UV_add_eq (r B s : ℤ) :
    U r B s + V r B s = 2 * (2 * r ^ 2 + B ^ 2) := by
  dsimp [U, V]
  ring

/-- Positivity of both factors; avoids explicit `|s|`. -/
lemma UV_pos {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    0 < U r B s ∧ 0 < V r B s := by
  have hprod : 0 < U r B s * V r B s := by
    rw [UV_mul_eq_five_mul_B4 hs]
    positivity
  have hsum : 0 < U r B s + V r B s := by
    rw [UV_add_eq]
    positivity
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos
  · exfalso
    have hsum_neg : U r B s + V r B s < 0 := add_neg hneg.1 hneg.2
    linarith

lemma U_odd {r B s : ℤ} (hr_odd : Odd r) (hB_odd : Odd B) :
    Odd (U r B s) := by
  dsimp [U]
  have h2r2 : Even (2 * r ^ 2) := (even_two : Even (2 : ℤ)).mul_right (r ^ 2)
  have h2s : Even (2 * s) := (even_two : Even (2 : ℤ)).mul_right s
  have hB2 : Odd (B ^ 2) := hB_odd.pow
  exact (h2r2.add_odd hB2).sub_even h2s

lemma V_odd {r B s : ℤ} (hr_odd : Odd r) (hB_odd : Odd B) :
    Odd (V r B s) := by
  dsimp [V]
  have h2r2 : Even (2 * r ^ 2) := (even_two : Even (2 : ℤ)).mul_right (r ^ 2)
  have h2s : Even (2 * s) := (even_two : Even (2 : ℤ)).mul_right s
  have hB2 : Odd (B ^ 2) := hB_odd.pow
  exact (h2r2.add_odd hB2).add_even h2s

/--
The real gcd lemma for the descent.

The approach in Q1401 has a gap: from the displayed congruences one gets that
an odd common prime divisor `p` satisfies `p ∣ 5*r^4`, not directly `p ∣ B^4`.
The final proof must then use `gcd(r,B)=1` to get `p=5`, and rule out `p=5`
from `2*r^2+B^2 ≡ 0 mod 5`, since `-2 ≡ 3` is not a square mod `5`.
-/
lemma UV_gcd_eq_one
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hr_odd : Odd r) (hB_odd : Odd B)
    (hgcd : Int.gcd r B = 1)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    Int.gcd (U r B s) (V r B s) = 1 := by
  -- Suggested proof:
  -- * Let p be a prime divisor of the gcd.
  -- * `U,V` odd gives p ≠ 2.
  -- * From p∣V-U=4s and p≠2, get p∣s.
  -- * From p∣U+V=2*(2*r^2+B^2) and p≠2, get p∣2*r^2+B^2.
  -- * Reducing the curve equation gives p∣5*r^4.
  -- * If p∣r, then p∣B, contradicting `hgcd`; hence p=5.
  -- * Mod 5, `2*r^2+B^2=0` and p∤r gives `(B/r)^2 = -2 = 3`, impossible.
  sorry

end DM1
```

## Q1403: `quartic_plus_both_odd` and the missing `4 ∣ B` case

The proposed proof still misses `r` odd and `4 ∣ B`.  If `B=4k`, then modulo `16` the RHS is `r^4`, and for odd `r` this is `1 mod 16`, compatible with being a square.

```lean
import Mathlib

namespace DM1

lemma zmod4_square_ne_three (x : ZMod 4) : x ^ 2 ≠ 3 := by
  fin_cases x <;> decide

lemma zmod16_square_ne_five (x : ZMod 16) : x ^ 2 ≠ 5 := by
  fin_cases x <;> decide

lemma rhs_mod4_r_even_B_odd
    (r B : ZMod 4)
    (hr : r = 0 ∨ r = 2)
    (hB : B = 1 ∨ B = 3) :
    r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4 = 3 := by
  rcases hr with rfl | rfl <;>
  rcases hB with rfl | rfl <;>
  decide

lemma rhs_mod16_r_odd_B_two_times_odd
    (r B : ZMod 16)
    (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 9 ∨ r = 11 ∨ r = 13 ∨ r = 15)
    (hB : B = 2 ∨ B = 6 ∨ B = 10 ∨ B = 14) :
    r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4 = 5 := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hB with rfl | rfl | rfl | rfl <;>
  decide

/-- Sanity check: the missing `4 ∣ B` case is not excluded mod 16. -/
example :
    ((1 : ZMod 16) ^ 4 + (1 : ZMod 16) ^ 2 * (4 : ZMod 16) ^ 2 -
      (4 : ZMod 16) ^ 4) = 1 := by
  decide

lemma B_four_dvd_impossible
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4)
    (hr_odd : r % 2 = 1)
    (h4 : (4 : ℤ) ∣ B) : False := by
  -- This is not a mod-16 contradiction.  It needs a separate 2-adic/descent lemma.
  sorry

lemma quartic_plus_both_odd_skeleton
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B) (hgcd : Int.gcd r B = 1)
    (heq : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    r % 2 = 1 ∧ B % 2 = 1 := by
  have hr_odd : r % 2 = 1 := by
    -- If `r` is even: either `B` is even, contradicting gcd=1, or `B` is odd,
    -- contradicting the mod-4 residue lemma above.
    sorry
  have hB_odd : B % 2 = 1 := by
    -- If `B` is even: either `B=2*odd`, use the mod-16 lemma above, or `4∣B`,
    -- use `B_four_dvd_impossible`.
    sorry
  exact ⟨hr_odd, hB_odd⟩

end DM1
```

## Q1404: non-baseness of the new solution `(v,u,a)`

This proof is mechanical once you keep the old non-base hypothesis and the old `4*r^2` identity.

```lean
import Mathlib

namespace DM1

def BaseZ (r B : ℤ) : Prop := r = 1 ∧ B = 1

/--
If the new solution `(v,u,a)` were base, then `u=v=1`, hence `b=1`,
`a^2=1`, `a=1`, `B=1`, and the old `4*r^2` identity gives `r=1`,
contradicting old non-baseness.
-/
lemma new_solution_nonbase
    {a b r B u v : ℤ}
    (hr_pos : 0 < r) (ha_pos : 0 < a)
    (habB : a * b = B)
    (hb_uv : b = u * v)
    (hnew : a ^ 2 = v ^ 4 + v ^ 2 * u ^ 2 - u ^ 4)
    (h4r : 4 * r ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + 4 * b ^ 4)
    (hnonbase : ¬ BaseZ r B) :
    ¬ BaseZ v u := by
  intro hbase
  rcases hbase with ⟨hv, hu⟩

  have hb1 : b = 1 := by
    rw [hb_uv, hu, hv]
    norm_num

  have ha_sq_one : a ^ 2 = 1 := by
    simpa [hu, hv] using hnew

  have ha1 : a = 1 := by
    nlinarith [ha_pos, ha_sq_one]

  have hB1 : B = 1 := by
    rw [← habB, ha1, hb1]
    norm_num

  have hr_sq_one : r ^ 2 = 1 := by
    have h4 : 4 * r ^ 2 = 4 := by
      simpa [ha1, hb1] using h4r
    nlinarith

  have hr1 : r = 1 := by
    nlinarith [hr_pos, hr_sq_one]

  exact hnonbase ⟨hr1, hB1⟩

end DM1
```

## Summary of exact remaining local lemmas

The mechanical algebra is above.  The exact non-mechanical lemmas to isolate are:

```lean
UV_gcd_eq_one
B_four_dvd_impossible
```

The current proposed proofs for these two are not complete as stated.  In particular, `UV_gcd_eq_one` needs the final mod-5 nonsquare step, and `B_four_dvd_impossible` is not a mod-16 contradiction.
