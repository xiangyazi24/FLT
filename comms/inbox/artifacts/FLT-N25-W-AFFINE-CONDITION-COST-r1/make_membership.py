from pathlib import Path
r=Path(__file__).parent
s=(r/'N25F_DedekindOrderMembership.lean').read_text()
d=(r/'CurveDedekindDivisorInput.lean').read_text()
(r/'DedekindOrderMembershipCheck.lean').write_text('import Mathlib.RingTheory.DedekindDomain.Factorization\nimport Mathlib.Algebra.Order.BigOperators.Group.Finset\n'+d[d.index('open scoped'):]+s[s.index('/-!'):]+''.join('\n#print axioms MazurProof.N25F_DedekindOrderMembership.'+n for n in ['fractionalIdeal_le_one_of_count_nonneg','fractionalIdeal_le_of_count_le','existsUnique_algebraMap_eq_of_count_nonneg','mem_fractionalIdeal_iff_count_le'])+'\n')
