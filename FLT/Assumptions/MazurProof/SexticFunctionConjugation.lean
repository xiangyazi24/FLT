import FLT.Assumptions.MazurProof.SexticMumfordBasis

/-!
# Hyperelliptic conjugation on the sextic function field

The affine involution `Y ↦ -Y` extends functorially from the coordinate ring
to the fraction field.  Packaging it as a ring equivalence makes conjugation
of units and fractional ideals available without choosing numerators and
denominators.
-/

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

def conjugateEquiv (M : Model K) :
    CoordinateRing M ≃+* CoordinateRing M where
  toFun := conjugate M
  invFun := conjugate M
  left_inv := conjugate_involutive M
  right_inv := conjugate_involutive M
  map_mul' := map_mul (conjugate M)
  map_add' := map_add (conjugate M)

@[simp] theorem conjugateEquiv_apply (M : Model K)
    (z : CoordinateRing M) :
    conjugateEquiv M z = conjugate M z := rfl

@[simp] theorem conjugateEquiv_symm (M : Model K) :
    (conjugateEquiv M).symm = conjugateEquiv M := by
  rfl

def functionConjugateEquiv (M : Model K) :
    FunctionField M ≃+* FunctionField M :=
  IsFractionRing.ringEquivOfRingEquiv (K := FunctionField M)
    (L := FunctionField M) (conjugateEquiv M)

@[simp] theorem functionConjugateEquiv_algebraMap
    (M : Model K) (z : CoordinateRing M) :
    functionConjugateEquiv M
        (algebraMap (CoordinateRing M) (FunctionField M) z) =
      algebraMap (CoordinateRing M) (FunctionField M) (conjugate M z) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (conjugateEquiv M) z

@[simp] theorem functionConjugateEquiv_symm (M : Model K) :
    (functionConjugateEquiv M).symm = functionConjugateEquiv M := by
  rw [functionConjugateEquiv,
    IsFractionRing.ringEquivOfRingEquiv_symm, conjugateEquiv_symm]

theorem functionConjugate_involutive (M : Model K) :
    Function.Involutive (functionConjugateEquiv M) := by
  intro z
  simpa only [functionConjugateEquiv_symm] using
    (functionConjugateEquiv M).symm_apply_apply z

def conjugateFunctionUnit (M : Model K) :
    (FunctionField M)ˣ →* (FunctionField M)ˣ :=
  Units.map (functionConjugateEquiv M).toRingHom

@[simp] theorem conjugateFunctionUnit_val (M : Model K)
    (z : (FunctionField M)ˣ) :
    (conjugateFunctionUnit M z : FunctionField M) =
      functionConjugateEquiv M (z : FunctionField M) := rfl

theorem conjugateFunctionUnit_involutive (M : Model K) :
    Function.Involutive (conjugateFunctionUnit M) := by
  intro z
  apply Units.ext
  exact functionConjugate_involutive M (z : FunctionField M)

end

end MazurProof.SexticMumford
