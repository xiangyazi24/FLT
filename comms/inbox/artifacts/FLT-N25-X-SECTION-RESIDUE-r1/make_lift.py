from pathlib import Path
r=Path(__file__).parent
s=(r/'N25F_DVRIntegralLift.lean').read_text()
(r/'DVRIntegralLiftCheck.lean').write_text(s+'\n#print axioms MazurProof.N25F_DVRIntegralLift.existsUnique_algebraMap_eq_of_log_nonneg\n#print axioms MazurProof.N25F_DVRIntegralLift.residue_eq_zero_iff_eq_zero_or_log_pos\n')
