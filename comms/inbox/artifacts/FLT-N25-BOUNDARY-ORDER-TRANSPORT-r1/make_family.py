from pathlib import Path
import re
r=Path(__file__).parent
base=(r/'N25F_FractionOrderDifference.lean').read_text()
equiv=Path('/workspace/shared/flt-n25-ord-ring-equiv/N25F_OrderRingEquiv.lean').read_text()
imports='import Mathlib.RingTheory.DedekindDomain.Dvr\nimport Mathlib.RingTheory.Ideal.Quotient.Operations\n'
equiv=equiv[equiv.index('set_option'):]
src=(r/'N25F_InfinityBoundaryOrderTransport.lean').read_text()
body=src[src.index('/-- The actual X boundary'):src.index('end MazurProof.N25F_InfinityBoundaryOrderTransport')]
out=imports+base+'\n'+equiv+'\nnamespace MazurProof.N25F_InfinityBoundaryOrderTransport\nopen N25F_OrderRingEquiv N25F_FractionOrderDifference\n'
for low,cap in [('x','X'),('yz','YZ'),('z','Z')]:
    start=body.index(f'/-- The actual {cap} boundary')
    end=body.index('/-- The actual YZ boundary') if cap=='X' else body.index('/-- The actual Z boundary') if cap=='YZ' else len(body)
    b=body[start:end].replace('(a : CurveField)', '(algebraMap N L a)').replace('(b : CurveField)', '(algebraMap N L b)')
    b=b.replace(f'  letI : IsFractionRing {cap}LocalRing CurveField := {low}LocalToFraction_isFractionRing\n','')
    b=b.replace(f'  letI : Algebra {cap}LocalRing CurveField := {low}LocalToFraction.toRingHom.toAlgebra\n','')
    b=b.replace(f'/-- The actual {cap} boundary',f'omit [IsDedekindDomain N] [IsDomain R] [IsDiscreteValuationRing R] in\ninclude {low}InfinityLocalizationEquiv in\n/-- The actual {cap} boundary',1)
    b=b.replace(f'/-- The existing signed {cap}',f'omit [IsDedekindDomain N] in\ninclude infinityNormalizationTo{cap}_injective {low}LocalToFraction_infinityNormalizationTo{cap} {low}InfinityLocalizationEquiv in\n/-- The existing signed {cap}',1)
    b=b.replace(f'{low}InfinityLocalizationEquiv_algebraMap]',f'{low}InfinityLocalizationEquiv_algebraMap {low}InfinityPrime {low}InfinityLocalizationEquiv]')
    b=b.replace(f'{low}InfinityNormalization_order, {low}InfinityNormalization_order]',f'{low}InfinityNormalization_order {low}InfinityPrime {low}InfinityLocalizationEquiv, {low}InfinityNormalization_order {low}InfinityPrime {low}InfinityLocalizationEquiv]')
    b=re.sub(r'  change WithZero.log \(Ring.ordFrac.*? = _\n', '', b, flags=re.S)
    b=b.replace('CurveFieldˣ', 'Lˣ')
    b=b.replace(f'{low}BoundaryOrder f', 'WithZero.log (Ring.ordFrac R (f.toMul : L))')
    for a,v in {'InfinityNormalization':'N',cap+'LocalRing':'R','CurveField':'L','infinityNormalizationTo'+cap:'(algebraMap N R)',low+'LocalToFraction':'(algebraMap R L)',low+'LocalFractionOrder':'(Ring.ordFrac R)'}.items():
        b=re.sub(r'\b'+a+r'\b',lambda _:v,b)
    out+=f'''
section {cap}
variable {{N R L : Type*}} [CommRing N] [IsDedekindDomain N]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra N L] [Algebra N R] [Algebra R L] [IsFractionRing R L]
variable (infinityNormalizationTo{cap}_injective : Function.Injective (algebraMap N R))
variable ({low}LocalToFraction_infinityNormalizationTo{cap} : ∀ a : N,
  algebraMap R L (algebraMap N R a) = algebraMap N L a)
variable ({low}InfinityPrime : Ideal N) [{low}InfinityPrime.IsPrime]
variable ({low}InfinityLocalizationEquiv : Localization.AtPrime {low}InfinityPrime ≃ₐ[N] R)
omit [IsDedekindDomain N] [IsDomain R] [IsDiscreteValuationRing R] in
private theorem {low}InfinityLocalizationEquiv_algebraMap (a : N) :
  {low}InfinityLocalizationEquiv (algebraMap N (Localization.AtPrime {low}InfinityPrime) a) = algebraMap N R a :=
  {low}InfinityLocalizationEquiv.commutes a
'''
    out+=b+f'end {cap}\n'
out+='\n#print axioms MazurProof.N25F_FractionOrderDifference.log_ordFrac_div\n'
for low in ['x','yz','z']:
    out+=f'#print axioms {low}InfinityNormalization_order\n#print axioms {low}BoundaryOrder_normalization_fraction\n'
out+='end MazurProof.N25F_InfinityBoundaryOrderTransport\n'
(r/'BoundaryOrderTransportFamilyCheck.lean').write_text(out)
