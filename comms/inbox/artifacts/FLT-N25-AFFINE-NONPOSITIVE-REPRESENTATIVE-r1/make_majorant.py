from pathlib import Path
r=Path(__file__).parent
s=(r/'N25F_DedekindPrincipalMajorant.lean').read_text()
(r/'DedekindPrincipalMajorantCheck.lean').write_text(s+'\n#print axioms MazurProof.N25F_DedekindPrincipalMajorant.exists_nonzero_regular_with_count_ge\n')
