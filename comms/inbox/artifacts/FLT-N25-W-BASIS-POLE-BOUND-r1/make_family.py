from pathlib import Path
import re
r=Path(__file__).parent
src=(r/'N25F_WBasisPoleBound.lean').read_text()
body=src[src.index('/-- A fixed actual basis'):src.index('end MazurProof.N25F_WBasisPoleBound')]
for a,b in [('wChart_finrank_polynomial_eq_four','hrank'),('xBoundaryOrder','xOrder'),('yzBoundaryOrder','yzOrder'),('zBoundaryOrder','zOrder')]:body=body.replace(a,b)
body=re.sub(r'\bW\b','A',body)
body=re.sub(r'\bP\b','(Polynomial (ZMod 2))',body)
body=re.sub(r'\bK\b','(FractionRing A)',body)
body=body.replace('Kˣ','((FractionRing A)ˣ)')
args={'wPolynomialBasis25Two':'A hrank','wPolynomialBasis25Two_ne_zero':'A hrank','wPolynomialBasisFunction25Two':'A hrank','wPolynomialBasisPoleBound25Two':'A hrank xOrder yzOrder zOrder','wPolynomialBasis_boundary_orders_bounded':'A hrank xOrder yzOrder zOrder'}
for n,a in args.items():
 body=re.sub(r'\b'+n+r'\b',n+' '+a,body)
 for kind in ['def','theorem']:body=body.replace(kind+' '+n+' '+a,kind+' '+n)
# Field notation for the basis API remains a partially applied basis.
body=body.replace('wPolynomialBasis25Two A hrank.ne_zero','(wPolynomialBasis25Two A hrank).ne_zero')
body=body.replace('theorem wPolynomialBasis25Two_ne_zero','omit [IsDomain A] in\ntheorem wPolynomialBasis25Two_ne_zero')
out='''import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_WBasisPoleBound
open scoped BigOperators
variable (A : Type*) [CommRing A] [IsDomain A]
  [Algebra (Polynomial (ZMod 2)) A] [Module.Finite (Polynomial (ZMod 2)) A]
  [Module.IsTorsionFree (Polynomial (ZMod 2)) A]
variable (hrank : Module.finrank (Polynomial (ZMod 2)) A = 4)
variable (xOrder yzOrder zOrder : Additive ((FractionRing A)ˣ) →+ ℤ)
'''+body
for n in args:out+='#print axioms '+n+'\n'
out+='end MazurProof.N25F_WBasisPoleBound\n'
(r/'WBasisPoleBoundFamilyCheck.lean').write_text(out)
