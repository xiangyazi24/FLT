from pathlib import Path
r=Path(__file__).parent
base=(r/'GenericNormMultiplicityCheck.lean').read_text().split('#print axioms count_relNorm_prime_zero_of_under_ne')[0]
s=(r/'N25F_InfinityNormMultiplicity.lean').read_text();body=s[s.index('/-- Every prime\'s norm coefficient'):s.index('end MazurProof.N25F_InfinityNormMultiplicity')]
repl={'InfinityNormalization':'S','BasePolynomial':'R','infinityBasePrime_prime':'hp','infinityBasePrime':'p','xInfinityPrime_ne_yzInfinityPrime':'hxy','xInfinityPrime_ne_zInfinityPrime':'hxz','yzInfinityPrime_ne_zInfinityPrime':'hyz','xInfinityPrime_relNorm':'hnx','yzInfinityPrime_relNorm':'hny','zInfinityPrime_relNorm':'hnz','xInfinityPrime':'x','yzInfinityPrime':'y','zInfinityPrime':'z'}
for a,b in repl.items():body=body.replace(a,b)
body=body.replace('infinity_primesOver_complete Q','hcomplete Q inferInstance inferInstance')
facts='hp hxy hxz hyz hnx hny hnz hcomplete'
body=body.replace('/-- Every prime\'s norm coefficient','include '+facts+' in\n/-- Every prime\'s norm coefficient').replace('/-- The coefficient of (T)','include '+facts+' in\n/-- The coefficient of (T)')
body=body.replace('    infinity_prime_norm_multiplicity I hI','    (infinity_prime_norm_multiplicity p x y z hp hxy hxz hyz hnx hny hnz hcomplete) I hI')
args='''
variable (p : Ideal R) (x y z : Ideal S) (hp : Prime p)
variable (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
variable (hnx : Ideal.relNorm R x = p) (hny : Ideal.relNorm R y = p) (hnz : Ideal.relNorm R z = p)
variable (hcomplete : ∀ Q : Ideal S, Q.IsPrime → Q.LiesOver p → Q = x ∨ Q = y ∨ Q = z)
'''
(r/'NormMultiplicityFamilyCheck.lean').write_text(base+args+body+'''#print axioms count_relNorm_prime_zero_of_under_ne
#print axioms count_relNorm_sum_three_of_primes
#print axioms infinity_prime_norm_multiplicity
#print axioms infinity_relNorm_multiplicity
end MazurProof.N25F_InfinityNormMultiplicity
''')
