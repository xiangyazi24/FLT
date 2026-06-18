/-
Top-level import file for the Mazur proof skeleton.
-/

-- Pure algebra: rational roots of unity, primitive roots, and finite group lemmas.
import FLT.Assumptions.MazurProof.RootsOfUnity
import FLT.Assumptions.MazurProof.CyclotomicLayer
import FLT.Assumptions.MazurProof.GroupTheory

-- Named axiom seams and the main torsion-bound derivation.
import FLT.Assumptions.MazurProof.Axioms
import FLT.Assumptions.MazurProof.TorsionFinite
import FLT.Assumptions.MazurProof.TorsionBound

-- Explicit N=10 obstruction computations and noncyclic exclusion interface.
import FLT.Assumptions.MazurProof.DescentObstruction
import FLT.Assumptions.MazurProof.NoncyclicN10
