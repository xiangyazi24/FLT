import FLT.Assumptions.MazurProof.RationalPointsN25QuotientHilbert

/-!
# Regression checks for the N25 Hilbert function

These checks keep the structural monomial count, the exact coefficient
comparison, and the eventual Hilbert function tied to their production
theorems.  The axiom reports must contain only Lean's standard logical axioms.
-/

open MazurProof.RationalPointsN25QuotientHilbert

#check @shiftedPiece_finrank
#print axioms shiftedPiece_finrank

#check @literalConePiece_finrank_eq_hilbertSeries_coeff
#print axioms literalConePiece_finrank_eq_hilbertSeries_coeff

#check @literalConePiece_finrank_eventually
#print axioms literalConePiece_finrank_eventually
