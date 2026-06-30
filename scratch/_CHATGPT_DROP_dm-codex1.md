# Q2618: compile-oriented proof of `euler_cofactor_coprime`

Target theorem:

```lean
theorem euler_cofactor_coprime
    {A D : Int}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2)
```

This proof follows route (1): prove the left cofactor

```text
F = 16*A^2 + D^2
```

is coprime to `12*A^2`, then transport coprimality to

```text
G = F - 12*A^2 = 4*A^2 + D^2.
```

The code uses only local Bezout helpers plus the existing local theorem

```lean
zmod3_sq_add_sq_eq_zero {x y : ZMod 3} (h : x^2 + y^2 = 0) : x=0 ∧ y=0
```

which you said is already in this namespace.

---

## Code

Paste inside `namespace MazurProof.RationalPointsN12.EulerSquarePair`.

```lean
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace MazurProof.RationalPointsN12.EulerSquarePair

private theorem q2618_isCoprime_mul_right_int {a b c : ℤ}
    (hab : IsCoprime a b) (hac : IsCoprime a c) :
    IsCoprime a (b * c) := by
  rcases hab with ⟨u, v, huv⟩
  rcases hac with ⟨r, s, hrs⟩
  refine ⟨u * r * a + u * s * c + v * r * b, v * s, ?_⟩
  calc
    (u * r * a + u * s * c + v * r * b) * a + (v * s) * (b * c)
        = (u * a + v * b) * (r * a + s * c) := by ring
    _ = 1 := by rw [huv, hrs]; ring

private theorem q2618_isCoprime_self_sub_right_int {x z : ℤ}
    (h : IsCoprime x z) :
    IsCoprime x (x - z) := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u + v, -v, ?_⟩
  calc
    (u + v) * x + (-v) * (x - z) = u * x + v * z := by ring
    _ = 1 := huv

private theorem q2618_isCoprime_two_of_odd_int {m : ℤ} (hm : Odd m) :
    IsCoprime m (2 : ℤ) := by
  rcases hm with ⟨k, hk⟩
  refine ⟨1, -k, ?_⟩
  rw [hk]
  ring

private theorem q2618_isCoprime_four_of_odd_int {m : ℤ} (hm : Odd m) :
    IsCoprime m (4 : ℤ) := by
  have h2 : IsCoprime m (2 : ℤ) := q2618_isCoprime_two_of_odd_int hm
  have h22 : IsCoprime m ((2 : ℤ) * 2) :=
    q2618_isCoprime_mul_right_int h2 h2
  simpa using h22

private theorem q2618_euler_left_odd {A D : ℤ} (hDodd : Odd D) :
    Odd (16 * A ^ 2 + D ^ 2) := by
  rcases hDodd with ⟨k, hk⟩
  refine ⟨8 * A ^ 2 + 2 * k ^ 2 + 2 * k, ?_⟩
  rw [hk]
  ring

/-- `16*A^2 + D^2` is coprime to `A`. -/
private theorem q2618_euler_left_coprime_A
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) A := by
  rcases hAD with ⟨u, v, huv⟩
  refine ⟨v ^ 2, u ^ 2 * A + 2 * u * v * D - 16 * v ^ 2 * A, ?_⟩
  calc
    v ^ 2 * (16 * A ^ 2 + D ^ 2)
        + (u ^ 2 * A + 2 * u * v * D - 16 * v ^ 2 * A) * A
        = (u * A + v * D) ^ 2 := by ring
    _ = 1 := by rw [huv]; ring

private theorem q2618_euler_left_coprime_A_sq
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (A ^ 2) := by
  have hA : IsCoprime (16 * A ^ 2 + D ^ 2) A :=
    q2618_euler_left_coprime_A hAD
  have hAA : IsCoprime (16 * A ^ 2 + D ^ 2) (A * A) :=
    q2618_isCoprime_mul_right_int hA hA
  simpa [pow_two] using hAA

/-- A local wrapper for the standard ZMod divisibility test. -/
private theorem q2618_zmod3_zero_iff_three_dvd (x : ℤ) :
    ((x : ZMod 3) = 0) ↔ (3 : ℤ) ∣ x := by
  simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd x 3)

/-- `3` does not divide `16*A^2 + D^2` if `A,D` are coprime. -/
private theorem q2618_not_three_dvd_euler_left
    {A D : ℤ} (hAD : IsCoprime A D) :
    ¬ (3 : ℤ) ∣ 16 * A ^ 2 + D ^ 2 := by
  intro h3
  have hcast0 : (((16 * A ^ 2 + D ^ 2 : ℤ) : ZMod 3) = 0) :=
    (q2618_zmod3_zero_iff_three_dvd (16 * A ^ 2 + D ^ 2)).2 h3
  have hsum : (A : ZMod 3) ^ 2 + (D : ZMod 3) ^ 2 = 0 := by
    norm_num at hcast0
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow] using hcast0
  rcases zmod3_sq_add_sq_eq_zero hsum with ⟨hA0, hD0⟩
  have h3A : (3 : ℤ) ∣ A :=
    (q2618_zmod3_zero_iff_three_dvd A).1 hA0
  have h3D : (3 : ℤ) ∣ D :=
    (q2618_zmod3_zero_iff_three_dvd D).1 hD0
  rcases hAD with ⟨u, v, huv⟩
  have h31 : (3 : ℤ) ∣ (1 : ℤ) := by
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right h3A u) (dvd_mul_of_dvd_right h3D v)
  norm_num at h31

/-- If `3 ∤ n`, then `n` and `3` are Bezout-coprime. -/
private theorem q2618_isCoprime_three_right_of_not_dvd {n : ℤ}
    (hn : ¬ (3 : ℤ) ∣ n) :
    IsCoprime n (3 : ℤ) := by
  have hnot0 : n % 3 ≠ 0 := by
    intro h0
    exact hn (Int.dvd_iff_emod_eq_zero.mpr h0)
  have hcases : n % 3 = 1 ∨ n % 3 = 2 := by
    have hnonneg : 0 ≤ n % 3 :=
      Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
    have hlt : n % 3 < 3 :=
      Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 3)
    omega
  rcases hcases with h1 | h2
  · refine ⟨1, -(n / 3), ?_⟩
    have hdiv := Int.ediv_add_emod n 3
    rw [h1] at hdiv
    omega
  · refine ⟨-1, n / 3 + 1, ?_⟩
    have hdiv := Int.ediv_add_emod n 3
    rw [h2] at hdiv
    omega

private theorem q2618_euler_left_coprime_three
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (3 : ℤ) :=
  q2618_isCoprime_three_right_of_not_dvd
    (q2618_not_three_dvd_euler_left hAD)

private theorem q2618_euler_left_coprime_twelve_mul_A_sq
    {A D : ℤ}
    (hDodd : Odd D) (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (12 * A ^ 2) := by
  have hA2 : IsCoprime (16 * A ^ 2 + D ^ 2) (A ^ 2) :=
    q2618_euler_left_coprime_A_sq hAD
  have h4 : IsCoprime (16 * A ^ 2 + D ^ 2) (4 : ℤ) :=
    q2618_isCoprime_four_of_odd_int (q2618_euler_left_odd hDodd)
  have h3 : IsCoprime (16 * A ^ 2 + D ^ 2) (3 : ℤ) :=
    q2618_euler_left_coprime_three hAD
  have h12raw : IsCoprime (16 * A ^ 2 + D ^ 2) ((4 : ℤ) * 3) :=
    q2618_isCoprime_mul_right_int h4 h3
  have h12 : IsCoprime (16 * A ^ 2 + D ^ 2) (12 : ℤ) := by
    simpa using h12raw
  have h : IsCoprime (16 * A ^ 2 + D ^ 2) ((12 : ℤ) * (A ^ 2)) :=
    q2618_isCoprime_mul_right_int h12 hA2
  simpa using h

/-- The two Euler cofactors are coprime. -/
theorem euler_cofactor_coprime
    {A D : Int}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) := by
  have hF12A : IsCoprime (16 * A ^ 2 + D ^ 2) (12 * A ^ 2) :=
    q2618_euler_left_coprime_twelve_mul_A_sq hDodd hAD
  have h := q2618_isCoprime_self_sub_right_int hF12A
  convert h using 1 <;> ring

end MazurProof.RationalPointsN12.EulerSquarePair
```

---

## API notes

1. The only Mathlib name that may vary by snapshot is the ZMod bridge:

```lean
ZMod.intCast_zmod_eq_zero_iff_dvd
```

If your pinned Mathlib has the arguments reversed, replace the local wrapper by:

```lean
private theorem q2618_zmod3_zero_iff_three_dvd (x : ℤ) :
    ((x : ZMod 3) = 0) ↔ (3 : ℤ) ∣ x := by
  simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd 3 x)
```

If the theorem is not in the `ZMod` namespace in your snapshot, search for:

```lean
#check ZMod.intCast_zmod_eq_zero_iff_dvd
#check intCast_zmod_eq_zero_iff_dvd
#check ZMod.intCast_eq_zero_iff_dvd
```

2. If your file already has `isCoprime_three_int_of_not_dvd`, you can replace `q2618_isCoprime_three_right_of_not_dvd` by that helper.  The needed orientation is:

```lean
¬ (3 : ℤ) ∣ n → IsCoprime n (3 : ℤ)
```

If your existing helper returns `IsCoprime (3 : ℤ) n`, use `.symm`.
