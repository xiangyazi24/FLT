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

/-- One of the two coprime fourth-power split branches. -/
private inductive FiveFourthSplit (A B q : ℤ) : Prop
  | left5 (m n : ℤ)
      (hmpos : 1 ≤ m) (hnpos : 1 ≤ n)
      (hq : q = m * n)
      (hA : A = 5 * m ^ 4)
      (hB : B = n ^ 4) : FiveFourthSplit A B q
  | right5 (m n : ℤ)
      (hmpos : 1 ≤ m) (hnpos : 1 ≤ n)
      (hq : q = m * n)
      (hA : A = m ^ 4)
      (hB : B = 5 * n ^ 4) : FiveFourthSplit A B q

/--
Odd denominator coprime-factor package.

This packages steps 1 and 2 from the outline:
`gcd(A,B)=1`, positivity, and the split of coprime positive factors of
`5*q^4` into one fourth power and one `5` times a fourth power.
-/
private lemma odd_coprime_five_fourth_split
    (p q t : ℤ)
    (hq : 2 ≤ q)
    (hqodd : ¬ (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4)
    (hAB : zphiA p q t * zphiB p q t = 5 * q ^ 4)
    (hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2))
    (hdiff : zphiB p q t - zphiA p q t = 4 * t) :
    FiveFourthSplit (zphiA p q t) (zphiB p q t) q := by
  -- Routine but verbose arithmetic package requested in step 1:
  -- * prove `Int.gcd (zphiA p q t) (zphiB p q t) = 1`;
  -- * use `hAB` and unique prime-factor exponents to split coprime factors.
  sorry

/--
The square-leg Pythagorean descent package for the branch
`A = 5m^4`, `B = n^4`, `q = mn`.

The hypotheses include the coefficient identity
`4*p^2 = (n^2-m^2)^2 + 4*m^4`, derived below from `A+B`.
The conclusion is exactly the smaller-denominator witness required by
`zphi_descent_step_odd_core`.
-/
private lemma pythagorean_descent_from_left5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m) (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  -- Step 4: set `r = (n^2-m^2)/2`, parametrize
  -- `p^2 = m^4 + r^2`, and produce the smaller solution.
  -- This is the primitive Pythagorean square-leg descent.
  sorry

/-- Symmetric branch, where `A = m^4`, `B = 5n^4`. -/
private lemma pythagorean_descent_from_right5
    (p q t m n : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (hmpos : 1 ≤ m) (hnpos : 1 ≤ n)
    (hqmn : q = m * n)
    (hcoeff : 4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  -- Same Pythagorean descent after swapping `m` and `n`.
  sorry

/-- Odd `q` core for the denominator descent. -/
private lemma zphi_descent_step_odd_core
    (p q t : ℤ)
    (hq : 2 ≤ q)
    (hqodd : ¬ (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4) :
    ∃ p' q' t' : ℤ,
      2 ≤ q' ∧
      Int.gcd p' q' = 1 ∧
      t' ^ 2 = p' ^ 4 + p' ^ 2 * q' ^ 2 - q' ^ 4 ∧
      q'.natAbs < q.natAbs := by
  have hAB : zphiA p q t * zphiB p q t = 5 * q ^ 4 :=
    zphi_AB_eq_5q4 p q t h
  have hsum : zphiA p q t + zphiB p q t = 2 * (2 * p ^ 2 + q ^ 2) :=
    zphi_A_add_B p q t
  have hdiff : zphiB p q t - zphiA p q t = 4 * t :=
    zphi_B_sub_A p q t

  obtain hsplit := odd_coprime_five_fourth_split p q t hq hqodd hcop h hAB hsum hdiff
  rcases hsplit with
    ⟨m, n, hmpos, hnpos, hqmn, hA, hB⟩ |
    ⟨m, n, hmpos, hnpos, hqmn, hA, hB⟩
  · -- Branch `A = 5m^4`, `B = n^4`.
    have hcoeff : 4 * p ^ 2 = (n ^ 2 - m ^ 2) ^ 2 + 4 * m ^ 4 := by
      -- From `A+B = 2(2p²+q²)` and `q=mn`:
      -- `5m⁴+n⁴ = 4p²+2m²n²`, hence the displayed identity.
      have hsum' : 5 * m ^ 4 + n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
        calc
          5 * m ^ 4 + n ^ 4 = zphiA p q t + zphiB p q t := by
            rw [hA, hB]
          _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
          _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
      nlinarith
    exact pythagorean_descent_from_left5 p q t m n hq hcop hmpos hnpos hqmn hcoeff
  · -- Branch `A = m^4`, `B = 5n^4`.
    have hcoeff : 4 * p ^ 2 = (m ^ 2 - n ^ 2) ^ 2 + 4 * n ^ 4 := by
      -- From `A+B = 2(2p²+q²)` and `q=mn`:
      -- `m⁴+5n⁴ = 4p²+2m²n²`, hence the displayed identity.
      have hsum' : m ^ 4 + 5 * n ^ 4 = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by
        calc
          m ^ 4 + 5 * n ^ 4 = zphiA p q t + zphiB p q t := by
            rw [hA, hB]
          _ = 2 * (2 * p ^ 2 + q ^ 2) := hsum
          _ = 2 * (2 * p ^ 2 + (m * n) ^ 2) := by rw [hqmn]
      nlinarith
    exact pythagorean_descent_from_right5 p q t m n hq hcop hmpos hnpos hqmn hcoeff
