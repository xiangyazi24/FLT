import FLT.Assumptions.MazurProof.TateNFDivision

/-!
# Nonsingularity of the order-9 Tate family

The finite order-18 obstruction records only `b ≠ 0` and the order-9 equation
`F9 b c = 0`.  This file proves that those two conditions already exclude all
singular Tate parameters over `ℚ`.
-/

namespace MazurProof.TateNonsingularN18

noncomputable section

open TateNFDivision

/-- The nontrivial factor of the discriminant of the Tate normal form. -/
def discriminantFactor (b c : ℚ) : ℚ :=
  16 * b ^ 2 - 8 * b * c ^ 2 - 20 * b * c + b +
    c ^ 4 - 3 * c ^ 3 + 3 * c ^ 2 - c

/-- Explicit discriminant of `y² + (1-c)xy - by = x³ - bx²`. -/
theorem tateCurve_discriminant (b c : ℚ) :
    (tateCurve b c).Δ = b ^ 3 * discriminantFactor b c := by
  simp [tateCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    discriminantFactor]
  ring

private def resultantCoeffF9 (b c : ℚ) : ℚ :=
  -768 * b * c ^ 4 - 3840 * b * c ^ 3 - 2304 * b * c ^ 2 -
    384 * b * c - 16 * b + 256 * c ^ 6 - 384 * c ^ 5 +
    96 * c ^ 4 + 160 * c ^ 3 - 56 * c ^ 2 - 20 * c - 1

private def resultantCoeffDiscriminant (b c : ℚ) : ℚ :=
  48 * b ^ 2 * c ^ 4 + 240 * b ^ 2 * c ^ 3 + 144 * b ^ 2 * c ^ 2 +
    24 * b ^ 2 * c + b ^ 2 + 8 * b * c ^ 6 + 60 * b * c ^ 5 -
    357 * b * c ^ 4 - 265 * b * c ^ 3 - 47 * b * c ^ 2 -
    2 * b * c + c ^ 8 + 130 * c ^ 7 + 235 * c ^ 6 +
    283 * c ^ 5 + 146 * c ^ 4 + 24 * c ^ 3 + c ^ 2

/-- The irreducible rational factor left by eliminating `b` from `F9` and the
discriminant factor. -/
def cubicFactor (c : ℚ) : ℚ := c ^ 3 - 129 * c ^ 2 - 24 * c - 1

/-- A kernel-checked Bézout identity for the elimination of `b`. -/
theorem F9_discriminant_resultant_identity (b c : ℚ) :
    resultantCoeffF9 b c * F9 b c +
        resultantCoeffDiscriminant b c * discriminantFactor b c =
      c ^ 9 * cubicFactor c := by
  simp [resultantCoeffF9, resultantCoeffDiscriminant, discriminantFactor,
    cubicFactor, F9]
  ring

private theorem cubicFactor_ne_zero (c : ℚ) : cubicFactor c ≠ 0 := by
  intro hc
  let p : ℤ := c.num
  let q : ℤ := c.den
  have hqpos : 0 < q := by
    dsimp [q]
    exact Int.natCast_pos.mpr c.pos
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hqpos)
  have hc_repr : c = (p : ℚ) / (q : ℚ) := by
    dsimp [p, q]
    exact (Rat.num_div_den c).symm
  have hhomQ :
      (p : ℚ) ^ 3 - 129 * (p : ℚ) ^ 2 * (q : ℚ) -
          24 * (p : ℚ) * (q : ℚ) ^ 2 - (q : ℚ) ^ 3 = 0 := by
    rw [hc_repr] at hc
    simp only [cubicFactor] at hc
    field_simp [hqQ] at hc
    nlinarith
  have hhom : p ^ 3 - 129 * p ^ 2 * q - 24 * p * q ^ 2 - q ^ 3 = 0 := by
    exact_mod_cast hhomQ
  have hcop : IsCoprime p q := by
    dsimp [p, q]
    exact Rat.isCoprime_num_den c
  rcases Int.even_or_odd p with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases Int.even_or_odd q with ⟨d, hd⟩ | ⟨d, hd⟩
  · rcases hcop with ⟨u, v, huv⟩
    rw [ha, hd] at huv
    ring_nf at huv
    omega
  · rw [ha, hd] at hhom
    ring_nf at hhom
    omega
  · rw [ha, hd] at hhom
    ring_nf at hhom
    omega
  · rw [ha, hd] at hhom
    ring_nf at hhom
    omega

/-- The order-9 equation with `b ≠ 0` automatically gives a nonsingular Tate
normal form over `ℚ`. -/
theorem tateCurve_discriminant_ne_zero_of_F9
    {b c : ℚ} (hb : b ≠ 0) (hF9 : F9 b c = 0) :
    (tateCurve b c).Δ ≠ 0 := by
  rw [tateCurve_discriminant]
  apply mul_ne_zero (pow_ne_zero 3 hb)
  intro hdisc
  have hres : c ^ 9 * cubicFactor c = 0 := by
    rw [← F9_discriminant_resultant_identity b c, hF9, hdisc]
    ring
  rcases mul_eq_zero.mp hres with hc9 | hcubic
  · have hc : c = 0 := by simpa using hc9
    subst c
    simp [F9] at hF9
    exact hb hF9
  · exact cubicFactor_ne_zero c hcubic

end

end MazurProof.TateNonsingularN18
