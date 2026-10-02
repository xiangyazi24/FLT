from pathlib import Path
import re
r=Path(__file__).parent
deps=(r/'LocalFractionFactorOrderCheck.lean').read_text().split('#print axioms')[0]
deps=deps.replace('import Mathlib.RingTheory.Localization.LocalizationLocalization',
  'import Mathlib.RingTheory.Ideal.Norm.RelNorm\nimport Lean.Elab.Tactic.Omega\nimport Mathlib.RingTheory.Localization.LocalizationLocalization',1)
variables='''
variable {A N L : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing N] [IsDedekindDomain N] [Algebra A N]
  [Module.Finite A N] [Module.IsTorsionFree A N]
  [Field L] [Algebra A L] [Algebra N L] [IsScalarTower A N L]
  [IsIntegralClosure N A L] [IsFractionRing N L]
  [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
  [FiniteDimensional (FractionRing A) L]
'''
def carriers(s):
    for a,b in [('BasePolynomial','A'),('BaseField','(FractionRing A)'),('InfinityNormalization','N'),('CurveField','L')]:
        s=s.replace(a,b)
    s=s.replace('(a : L)', '(algebraMap N L a)').replace('(b : L)', '(algebraMap N L b)')
    return s
norm=(r/'N25F_InfinityNormFraction.lean').read_text()
norm=norm[norm.index('/-- Integral and fixed-field'):norm.index('end MazurProof.N25F_InfinityNormFraction')]
norm=norm.replace('/-- Integral and fixed-field', 'omit [IsFractionRing N L] in\n/-- Integral and fixed-field')
out=deps+'\n'+variables+'\nnamespace MazurProof.N25F_InfinityNormFraction\n'+carriers(norm)+'end MazurProof.N25F_InfinityNormFraction\n'
s=(r/'N25F_InfinityNormBoundarySum.lean').read_text()
s=s[s.index('/-- The genuine fraction-field order'):s.index('end MazurProof.N25F_InfinityNormBoundarySum')]
s=carriers(s)
start=s.index('  have hp : infinityBasePrime')
end=s.index('  rw [xBoundaryOrder_normalization_fraction',start)
s=s[:start]+s[end:]
for a,b in [('xInfinityPrime_ne_bot','hx'),('yzInfinityPrime_ne_bot','hy'),('zInfinityPrime_ne_bot','hz'),
 ('infinityBasePrime','p'),('xInfinityPrime','x'),('yzInfinityPrime','y'),('zInfinityPrime','z'),
 ('xBoundaryOrder_normalization_fraction','hxf'),('yzBoundaryOrder_normalization_fraction','hyf'),
 ('zBoundaryOrder_normalization_fraction','hzf'),('infinity_relNorm_multiplicity','hmult')]:
    s=s.replace(a,b)
# Explicit generic parameters replace fixed production constants.
s=s.replace('exists_normalization_fraction (f.toMul', 'exists_normalization_fraction (N := N) (f.toMul')
s=s.replace('infinityBaseFractionOrder (Algebra.norm','infinityBaseFractionOrder p (Algebra.norm')
s=s.replace('/-- For the fixed function', 'include hp hx hy hz hmult hxf hyf hzf in\n/-- For the fixed function')
header='''
namespace MazurProof.N25F_InfinityNormBoundarySum
open UniqueFactorizationMonoid N25F_LocalFactorOrder N25F_LocalFractionFactorOrder N25F_InfinityNormFraction
variable (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
variable (x y z : Ideal N) [x.IsPrime] [y.IsPrime] [z.IsPrime]
variable (hx : x ≠ ⊥) (hy : y ≠ ⊥) (hz : z ≠ ⊥)
variable (hmult : ∀ I : Ideal N, I ≠ ⊥ →
  (normalizedFactors (Ideal.relNorm A I)).count p =
  (normalizedFactors I).count x + (normalizedFactors I).count y + (normalizedFactors I).count z)
variable (xBoundaryOrder yzBoundaryOrder zBoundaryOrder : Additive Lˣ → ℤ)
variable (hxf : ∀ a b : N, a ≠ 0 → b ≠ 0 → ∀ f : Additive Lˣ,
  (f.toMul : L) = algebraMap N L a / algebraMap N L b →
  xBoundaryOrder f = ((Ring.ord (Localization.AtPrime x)
    (algebraMap N (Localization.AtPrime x) a)).toNat : ℤ) -
    ((Ring.ord (Localization.AtPrime x) (algebraMap N (Localization.AtPrime x) b)).toNat : ℤ))
variable (hyf : ∀ a b : N, a ≠ 0 → b ≠ 0 → ∀ f : Additive Lˣ,
  (f.toMul : L) = algebraMap N L a / algebraMap N L b →
  yzBoundaryOrder f = ((Ring.ord (Localization.AtPrime y)
    (algebraMap N (Localization.AtPrime y) a)).toNat : ℤ) -
    ((Ring.ord (Localization.AtPrime y) (algebraMap N (Localization.AtPrime y) b)).toNat : ℤ))
variable (hzf : ∀ a b : N, a ≠ 0 → b ≠ 0 → ∀ f : Additive Lˣ,
  (f.toMul : L) = algebraMap N L a / algebraMap N L b →
  zBoundaryOrder f = ((Ring.ord (Localization.AtPrime z)
    (algebraMap N (Localization.AtPrime z) a)).toNat : ℤ) -
    ((Ring.ord (Localization.AtPrime z) (algebraMap N (Localization.AtPrime z) b)).toNat : ℤ))
'''
out+=header+s+'''
#print axioms MazurProof.N25F_InfinityNormFraction.infinity_norm_normalization
#print axioms MazurProof.N25F_InfinityNormFraction.infinity_norm_fraction
#print axioms MazurProof.N25F_InfinityNormFraction.exists_normalization_fraction
#print axioms MazurProof.N25F_LocalFractionFactorOrder.log_ordFrac_atPrime_div
#print axioms infinityBaseFractionOrder
#print axioms infinity_norm_boundary_order_sum
end MazurProof.N25F_InfinityNormBoundarySum
'''
(r/'InfinityNormBoundarySumFamilyCheck.lean').write_text(out)
