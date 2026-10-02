from pathlib import Path
r=Path(__file__).parent
s=(r/'MathlibPolynomialBasisInput.lean').read_text()
h=(r/'N25F_PolynomialBasisWindow.lean').read_text()
(r/'PolynomialBasisWindowCheck.lean').write_text('import Mathlib.Algebra.Polynomial.Basic\nimport Mathlib.LinearAlgebra.Basis.Defs\nimport Mathlib.RingTheory.AlgebraTower\n'+s[s.index('open Module'):]+h[h.index('/-!'):]+ '\n#print axioms MazurProof.N25F_PolynomialBasisWindow.polynomial_basis_window_linearIndependent\n')
