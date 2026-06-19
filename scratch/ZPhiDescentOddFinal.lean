import Mathlib

/-- Left Pellian factor. -/
private def zphiA (p q t : ℤ) : ℤ :=
  2 * p ^ 2 + q ^ 2 - 2 * t

/-- Right Pellian factor. -/
private def zphiB (p q t : ℤ) : ℤ :=
  2 * p ^ 2 + q ^ 2 + 2 * t

/-- Pellian product identity. -/
private lemma zphi_AB_eq_5q4 (p q t : ℤ)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    zphiA p q t * zphiB p q t = 5 * q ^ 4 := by
  dsimp [zphiA, zphiB]
  nlinarith

/-- Sum of the two Pellian factors. -/
private lemma zphi_A_add_B (p q t : ℤ) :
    zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2) := by
  dsimp [zphiA, zphiB]
  ring

/-- Difference of the two Pellian factors. -/
private lemma zphi_B_sub_A (p q t : ℤ) :
    zphiB p q t - zphiA p q t = 4 * t := by
  dsimp [zphiA, zphiB]
  ring

/-- Algebraic coefficient comparison in the branch `A = 5m^4`, `B = n^4`. -/
private lemma coeff_identity_left5
    (p q t m n : ℤ)
    (hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hqmn : q = m * n)
    (hA : zphiA p q t = 5 * m ^ 4)
    (hB : zphiB p q t = n ^ 4) :
    4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4 := by
  have hsum' : 5 * m ^ 4 + n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
    calc
      5 * m ^ 4 + n ^ 4 = zphiA p q t + zphiB p q t := by
        rw [hA, hB]
      _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
      _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
  nlinarith

/-- Algebraic coefficient comparison in the branch `A = m^4`, `B = 5n^4`. -/
private lemma coeff_identity_right5
    (p q t m n : ℤ)
    (hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hqmn : q = m * n)
    (hA : zphiA p q t = m ^ 4)
    (hB : zphiB p q t = 5 * n ^ 4) :
    4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4 := by
  have hsum' : m ^ 4 + 5 * n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
    calc
      m ^ 4 + 5 * n ^ 4 = zphiA p q t + zphiB p q t := by
        rw [hA, hB]
      _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
      _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
  nlinarith

/--
The actual missing descent package after the coefficient identity.

This is not a gcd bookkeeping lemma.  It is the primitive Pythagorean
parametrization plus the self-descent that turns
`4p² = (n²-m²)² + 4m⁴` into a smaller solution of
`t² = p⁴ + p²q² - q⁴`.
-/
private axiom pythagorean_square_leg_self_descent_left5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs

/-- Symmetric missing descent package for the branch `A=m^4`, `B=5n^4`. -/
private axiom pythagorean_square_leg_self_descent_right5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m)
    (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs
