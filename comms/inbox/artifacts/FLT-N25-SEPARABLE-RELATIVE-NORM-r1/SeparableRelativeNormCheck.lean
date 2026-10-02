import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.FieldTheory.SeparableClosure

/-! Relative ideal norm at a prime for a finite separable fraction-field
extension. This route does not assume a perfect base fraction field. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_SeparableRelativeNorm

/-- The normal closure of a separable extension remains separable even
when the ambient algebraic closure is inseparable over the base. -/
theorem normalClosure_isSeparable
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (IntermediateField.normalClosure K L M) := by
  change Algebra.IsSeparable K (⨆ f : L →ₐ[K] M, f.fieldRange : IntermediateField K M)
  letI : ∀ f : L →ₐ[K] M, Algebra.IsSeparable K f.fieldRange := fun f =>
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  infer_instance


section Domains
variable (R S : Type*) [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]
local instance : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra _ _
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
local notation "K" => FractionRing R
local notation "L" => FractionRing S
local notation "E" => IntermediateField.normalClosure K L (AlgebraicClosure L)
local notation "T" => Ring.NormalClosure R S
local instance : Algebra K (FractionRing T) := FractionRing.liftAlgebra _ _
local instance : Algebra L (FractionRing T) := FractionRing.liftAlgebra _ _

local instance : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
local instance : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl
local instance : Algebra T E := inferInstanceAs (Algebra (integralClosure S E) E)
local instance : IsScalarTower S T E := inferInstanceAs (IsScalarTower S (integralClosure S E) E)
local instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E
local instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E
local instance : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
local instance : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr <|
  (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)
local instance : FiniteDimensional L E := Module.Finite.right K L E
local instance : IsFractionRing T E := integralClosure.isFractionRing_of_finite_extension L E
local instance : Algebra.IsSeparable K E := normalClosure_isSeparable
local instance : Algebra.IsSeparable L E := Algebra.isSeparable_tower_top_of_isSeparable K L E
local instance : IsGalois K E := ⟨⟩

/-- The ring normal closure has a Galois fraction field under separability alone. -/
theorem normalClosure_isGalois_of_separable : IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _

/-- Its integral normalization is finite over S without a perfectness premise. -/
theorem normalClosure_finite_of_separable : Module.Finite S T :=
  IsIntegralClosure.finite S L E T

/-- The same normal closure is Dedekind under the actual separability premise. -/
theorem normalClosure_isDedekindDomain_of_separable : IsDedekindDomain T :=
  integralClosure.isDedekindDomain S L E

attribute [local instance] normalClosure_isGalois_of_separable
  normalClosure_finite_of_separable normalClosure_isDedekindDomain_of_separable
local instance : Module.Finite R T := Module.Finite.trans S T

/-- A maximal prime's relative norm uses its residue degree for every finite
separable fraction-field extension; the base fraction field need not be perfect. -/
theorem relNorm_prime_of_separable (P : Ideal S) (p : Ideal R)
    [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg P := by
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  letI : Q.IsMaximal := hQ₁
  letI : Q.LiesOver P := hQ₂
  letI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  letI : IsGalois L (FractionRing T) := IsGalois.tower_top_of_isGalois K L (FractionRing T)
  rwa [← Ideal.relNorm_relNorm R S, Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    Ideal.inertiaDeg_algebra_tower p P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr <| Ideal.inertiaDeg_pos P Q

end Domains
end MazurProof.N25F_SeparableRelativeNorm

#check @MazurProof.N25F_SeparableRelativeNorm.relNorm_prime_of_separable
#print axioms MazurProof.N25F_SeparableRelativeNorm.normalClosure_isSeparable
#print axioms MazurProof.N25F_SeparableRelativeNorm.normalClosure_isGalois_of_separable
#print axioms MazurProof.N25F_SeparableRelativeNorm.normalClosure_finite_of_separable
#print axioms MazurProof.N25F_SeparableRelativeNorm.normalClosure_isDedekindDomain_of_separable
#print axioms MazurProof.N25F_SeparableRelativeNorm.relNorm_prime_of_separable
