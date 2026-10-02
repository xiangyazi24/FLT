from pathlib import Path
r=Path(__file__).parent
b=(r/'BinaryResidueOrderInput.lean').read_text()
s=(r/'N25F_BinaryResidueCancellation.lean').read_text()
(r/'BinaryResidueCancellationCheck.lean').write_text(b+'\n'+s[s.index('/-!'):]+ '\n#print axioms MazurProof.N25F_BinaryResidueCancellation.log_ordFrac_sub_gt_of_log_eq\n')
