from pathlib import Path
r = Path(__file__).parent
base = (r/'N25F_LocalFactorOrder.lean').read_text()
base = base.replace('import Mathlib.RingTheory.DedekindDomain.Dvr',
  'import Mathlib.RingTheory.Ideal.Norm.RelNorm\nimport Mathlib.RingTheory.DedekindDomain.Dvr')
s = (r/'N25F_InfinityPrincipalNormOrder.lean').read_text()
body = s[s.index('/-- A principal ideal'):s.index('end MazurProof.N25F_InfinityPrincipalNormOrder')]
start = body.index('  have hp : infinityBasePrime')
end = body.index('  rw [ord_algebraMap_eq_factor_count', start)
body = body[:start] + body[end:]
for a,b in {'InfinityNormalization':'S', 'BasePolynomial':'R',
 'infinityBasePrime':'p', 'xInfinityPrime_ne_bot':'hx',
 'yzInfinityPrime_ne_bot':'hy', 'zInfinityPrime_ne_bot':'hz',
 'xInfinityPrime':'x', 'yzInfinityPrime':'y', 'zInfinityPrime':'z',
 'infinity_relNorm_multiplicity':'hmult'}.items():
    body = body.replace(a,b)
header = '''
namespace MazurProof.N25F_InfinityPrincipalNormOrder
open UniqueFactorizationMonoid N25F_LocalFactorOrder
variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]
variable (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
  (x y z : Ideal S) [x.IsPrime] [y.IsPrime] [z.IsPrime]
  (hx : x ≠ ⊥) (hy : y ≠ ⊥) (hz : z ≠ ⊥)
variable (hmult : ∀ I : Ideal S, I ≠ ⊥ →
  (normalizedFactors (Ideal.relNorm R I)).count p =
  (normalizedFactors I).count x + (normalizedFactors I).count y +
  (normalizedFactors I).count z)
include hp hx hy hz hmult in
'''
audit = '''
#print axioms MazurProof.N25F_LocalFactorOrder.local_length_eq_factor_count
#print axioms MazurProof.N25F_LocalFactorOrder.ord_algebraMap_eq_factor_count
#print axioms infinity_intNorm_local_order
end MazurProof.N25F_InfinityPrincipalNormOrder
'''
(r/'PrincipalNormOrderFamilyCheck.lean').write_text(base+header+body+audit)
