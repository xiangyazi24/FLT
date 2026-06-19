import Mathlib

/-!
# Denominator theorem: rational points on y²=x³+x²-x have integer x-coordinate.

The proof reduces to the denominator quartic via:
1. Clearing denominators → b²|q³ (b=w.den, q=u.den)  
2. Valuation argument → q is a perfect square (axiomatized here)
3. Coprime product = square → Int.sq_of_isCoprime
4. Denominator quartic → contradiction if q≥2
-/

-- The valuation step: this is the only real gap.
-- From b²|q³ with gcd(a,b)=1 and the equation a²q³=b²N with gcd(N,q)=1:
-- 3v_ℓ(q) = 2v_ℓ(b) for all primes ℓ|q → v_ℓ(q) even → q is a perfect square.
-- Plus: b = d³ (where q=d²) and m=b/d³=1 (from gcd(a,b)=1).
-- So a² = N = p(p²+pd²-d⁴) with gcd(p,d)=1.
axiom clearing_denominators_gives_quartic (p : ℤ) (q : ℕ)
    (hq : 2 ≤ q) (hcop : p.natAbs.Coprime q)
    (w : ℚ) (hw : w ^ 2 = (p : ℚ) / q * ((p : ℚ) ^ 2 / q ^ 2 + (p : ℚ) / q - 1)) :
    ∃ d a : ℤ, 2 ≤ d ∧ q = d.natAbs ^ 2 ∧ 
      a ^ 2 = p * (p ^ 2 + p * d ^ 2 - d ^ 4) ∧ Int.gcd p d = 1

-- The denominator quartic: already proved in DenominatorQuartic.lean
-- (using zphi_descent_step which uses FourthPowerSplit + PythagoreanDescentTail)
axiom no_denominator_quartic_imported (s q t : ℤ) (hq : 2 ≤ q) 
    (hcop : Int.gcd s q = 1) (h : t ^ 2 = s ^ 4 + s ^ 2 * q ^ 2 - q ^ 4) : False

theorem rat_den_one_of_curve (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1 := by
  by_contra hden
  have hq : 2 ≤ u.den := by omega
  let p := u.num
  let q := u.den
  -- u = p/q, curve equation becomes w² = p/q·(p²/q²+p/q-1)
  have hu_eq : u = (p : ℚ) / q := by exact (Rat.num_div_den u).symm
  -- Get the quartic data from clearing denominators
  obtain ⟨d, a, hd, hq_sq, ha, hcop_pd⟩ := 
    clearing_denominators_gives_quartic p q hq (Rat.reduced u) w (by rw [hu_eq] at h; convert h using 1; push_cast; ring)
  -- a² = p(p²+pd²-d⁴). gcd(p,d)=1. Int.sq_of_isCoprime:
  have hcop_factors : IsCoprime p (p ^ 2 + p * d ^ 2 - d ^ 4) := ⟨p + d ^ 2, -1, by ring⟩
  obtain ⟨s, hs | hs⟩ := Int.sq_of_isCoprime hcop_factors ha
  · -- p = s². Then p²+pd²-d⁴ = s⁴+s²d²-d⁴ = t² (a square since a²=p·(...))
    obtain ⟨t, ht | ht⟩ := Int.sq_of_isCoprime hcop_factors.symm (by linarith)
    · -- t² = s⁴+s²d²-d⁴. Denominator quartic!
      exact no_denominator_quartic_imported s d t hd hcop_pd (by nlinarith)
    · -- p²+pd²-d⁴ = -t². But p²+pd²-d⁴ > 0 for the relevant range.
      sorry -- handle negative case
  · -- p = -s². Then u = -s²/d² < 0. 
    sorry -- handle negative squareclass case

