/-
Top-level import file for the Mazur proof skeleton.
-/
module

-- Pure algebra: rational roots of unity, primitive roots, and finite group lemmas.
public import FLT.Assumptions.MazurProof.RootsOfUnity
public import FLT.Assumptions.MazurProof.CyclotomicLayer
public import FLT.Assumptions.MazurProof.GroupTheory

-- Named axiom seams and the main torsion-bound derivation.
public import FLT.Assumptions.MazurProof.Axioms
public import FLT.Assumptions.MazurProof.TorsionFinite
public import FLT.Assumptions.MazurProof.TorsionBound

-- Explicit N=10 obstruction computations and noncyclic exclusion interface.
public import FLT.Assumptions.MazurProof.DescentObstruction
public import FLT.Assumptions.MazurProof.NoncyclicN10
