from pathlib import Path
r=Path(__file__).parent
base=(r/'PrincipalOrderAdditionCheck.lean').read_text().split('#print axioms')[0]
ded=Path('/workspace/shared/flt-n25-divisor-length/check_project/FLT/Assumptions/MazurProof/CurveDedekindDivisor.lean').read_text()
ded=ded[ded.index('open scoped'):]
out=base+'\n'+ded+'''
namespace ProjectiveAdditionFamily
open scoped nonZeroDivisors
open MazurProof.N25F_PrincipalOrderAddition
inductive Boundary | X | YZ | Z

variable {R B₁ B₂ B₃ A : Type*} [CommRing R] [IsDedekindDomain R]
variable [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra B₁ (FractionRing R)] [IsFractionRing B₁ (FractionRing R)]
variable [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra B₂ (FractionRing R)] [IsFractionRing B₂ (FractionRing R)]
variable [CommRing B₃] [IsDomain B₃] [IsDiscreteValuationRing B₃]
  [Algebra B₃ (FractionRing R)] [IsFractionRing B₃ (FractionRing R)]
variable (e : Sum Boundary (IsDedekindDomain.HeightOneSpectrum R) ≃ A)

def boundaryDivisor (f : Additive (FractionRing R)ˣ) : Boundary →₀ ℤ :=
  Finsupp.single .X (WithZero.log (Ring.ordFrac B₁ (f.toMul : FractionRing R))) +
  Finsupp.single .YZ (WithZero.log (Ring.ordFrac B₂ (f.toMul : FractionRing R))) +
  Finsupp.single .Z (WithZero.log (Ring.ordFrac B₃ (f.toMul : FractionRing R)))

def principal (f : Additive (FractionRing R)ˣ) : A →₀ ℤ :=
  Finsupp.domCongr e (Finsupp.sumFinsuppAddEquivProdFinsupp.symm
    (boundaryDivisor (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) f,
      MazurProof.CurveDedekindDivisor.principalDivisor (R := R) f))

theorem coefficient_boundary (f : Additive (FractionRing R)ˣ) (t : Boundary) :
    principal (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) e f (e (.inl t)) =
      boundaryDivisor (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) f t := by
  simp [principal, Finsupp.domCongr]

theorem coefficient_affine (f : Additive (FractionRing R)ˣ)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    principal (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) e f (e (.inr v)) =
      MazurProof.CurveDedekindDivisor.principalDivisor (R := R) f v := by
  simp [principal, Finsupp.domCongr]

private theorem boundary_add {B L : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    (f g h : Additive Lˣ) (hadd : (h.toMul : L) = (f.toMul : L) + (g.toMul : L)) :
    min (WithZero.log (Ring.ordFrac B (f.toMul : L)))
      (WithZero.log (Ring.ordFrac B (g.toMul : L))) ≤
        WithZero.log (Ring.ordFrac B (h.toMul : L)) := by
  rw [hadd]
  exact log_ordFrac_add_ge_min _ _ f.toMul.ne_zero g.toMul.ne_zero
    (by rw [← hadd]; exact h.toMul.ne_zero)

theorem projective_add_ge_min (f g h : Additive (FractionRing R)ˣ)
    (hadd : (h.toMul : FractionRing R) = (f.toMul : FractionRing R) + (g.toMul : FractionRing R))
    (a : A) :
    min (principal (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) e f a)
      (principal (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) e g a) ≤
      principal (B₁ := B₁) (B₂ := B₂) (B₃ := B₃) e h a := by
  obtain ⟨s, rfl⟩ := e.surjective a
  cases s with
  | inl t =>
      simp only [coefficient_boundary]
      cases t with
      | X => simpa [boundaryDivisor] using boundary_add (B := B₁) f g h hadd
      | YZ => simpa [boundaryDivisor] using boundary_add (B := B₂) f g h hadd
      | Z => simpa [boundaryDivisor] using boundary_add (B := B₃) f g h hadd
  | inr v =>
      simp only [coefficient_affine]
      change min (FractionalIdeal.count (FractionRing R) v
          (FractionalIdeal.spanSingleton R⁰ (f.toMul : FractionRing R)))
        (FractionalIdeal.count (FractionRing R) v
          (FractionalIdeal.spanSingleton R⁰ (g.toMul : FractionRing R))) ≤
        FractionalIdeal.count (FractionRing R) v
          (FractionalIdeal.spanSingleton R⁰ (h.toMul : FractionRing R))
      rw [hadd]
      exact count_spanSingleton_add_ge_min v _ _ f.toMul.ne_zero g.toMul.ne_zero
        (by rw [← hadd]; exact h.toMul.ne_zero)

#print axioms MazurProof.N25F_PrincipalOrderAddition.log_ordFrac_add_ge_min
#print axioms MazurProof.N25F_PrincipalOrderAddition.count_spanSingleton_eq_log_ordFrac
#print axioms MazurProof.N25F_PrincipalOrderAddition.count_spanSingleton_add_ge_min
#print axioms projective_add_ge_min
end ProjectiveAdditionFamily
'''
(r/'ProjectiveAdditionFamilyCheck.lean').write_text(out)
