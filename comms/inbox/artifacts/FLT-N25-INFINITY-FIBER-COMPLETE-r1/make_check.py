from pathlib import Path
r=Path(__file__).parent;s=(r/'N25F_InfinityFiberComplete.lean').read_text();s='import InfinityNormalizationCheck\n'+'\n'.join(l for l in s.splitlines() if not l.startswith('import FLT.'))+'\n'
a=s.index('open N25F_RationalBaseInversion');b=s.index('/-- The reciprocal base embeds',a)
s=s[:a]+'''open N25F_RationalBaseInversion N25F_InfinityBaseMaps N25F_InfinityNormalization
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
attribute [local instance] infinityPolynomialAlgebra

'''+s[b:]
pos='/-- The entire infinity fiber has ramification-inertia weight four. -/'
s=s.replace(pos,'''variable [Module.Finite BasePolynomial InfinityNormalization]
variable (infinityBasePrime : Ideal BasePolynomial) [infinityBasePrime.IsPrime]
variable (hRank : Module.finrank BasePolynomial InfinityNormalization = 4)
include hRank in
'''+pos)
s=s.replace('infinityNormalization_finrank_eq_four','hRank')
pos='/-- The three actual center primes exhaust the entire fiber above (T). -/'
s=s.replace(pos,'''variable (xInfinityPrime yzInfinityPrime zInfinityPrime : Ideal InfinityNormalization)
variable [xInfinityPrime.IsPrime] [yzInfinityPrime.IsPrime] [zInfinityPrime.IsPrime]
variable [xInfinityPrime.LiesOver infinityBasePrime] [yzInfinityPrime.LiesOver infinityBasePrime]
variable [zInfinityPrime.LiesOver infinityBasePrime]
variable (xInfinityPrime_ne_yzInfinityPrime : xInfinityPrime ≠ yzInfinityPrime)
variable (xInfinityPrime_ne_zInfinityPrime : xInfinityPrime ≠ zInfinityPrime)
variable (yzInfinityPrime_ne_zInfinityPrime : yzInfinityPrime ≠ zInfinityPrime)
variable (xInfinityPrime_ramificationIdx_eq_one : xInfinityPrime.ramificationIdx' BasePolynomial = 1)
variable (yzInfinityPrime_ramificationIdx_eq_one : yzInfinityPrime.ramificationIdx' BasePolynomial = 1)
variable (zInfinityPrime_ramificationIdx_eq_two : zInfinityPrime.ramificationIdx' BasePolynomial = 2)
variable (xInfinityPrime_inertiaDeg_eq_one : xInfinityPrime.inertiaDeg' BasePolynomial = 1)
variable (yzInfinityPrime_inertiaDeg_eq_one : yzInfinityPrime.inertiaDeg' BasePolynomial = 1)
variable (zInfinityPrime_inertiaDeg_eq_one : zInfinityPrime.inertiaDeg' BasePolynomial = 1)
include hRank xInfinityPrime_ne_yzInfinityPrime xInfinityPrime_ne_zInfinityPrime
  yzInfinityPrime_ne_zInfinityPrime xInfinityPrime_ramificationIdx_eq_one
  yzInfinityPrime_ramificationIdx_eq_one zInfinityPrime_ramificationIdx_eq_two
  xInfinityPrime_inertiaDeg_eq_one yzInfinityPrime_inertiaDeg_eq_one zInfinityPrime_inertiaDeg_eq_one in
'''+pos)
s=s.replace('have hs : ∑ p, w p = 4 := infinityFiber_sum','have hs : ∑ p, w p = 4 := infinityFiber_sum infinityBasePrime hRank')
s=s.replace('end MazurProof.N25F_InfinityFiberComplete','''#print axioms infinityNormalization_algebraMap_injective
#print axioms infinityNormalization_isTorsionFree
#print axioms infinityNormalization_flat
#print axioms infinityFiber_sum
#print axioms infinity_primesOver_complete
end MazurProof.N25F_InfinityFiberComplete''')
(r/'InfinityFiberCompleteCheck.lean').write_text(s)
