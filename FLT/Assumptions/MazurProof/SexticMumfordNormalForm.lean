import FLT.Assumptions.MazurProof.SexticMumfordBasis

/-!
# First normalization step for sextic Mumford ideals

Before choosing a two-generator `K[X]`-basis, a fractional ideal may be
cleared of denominators by a single nonzero element of the coordinate ring.
This is the first, representation-independent step in the normal-form
argument.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Every invertible fractional ideal of the sextic coordinate ring becomes
an integral ideal after multiplication by one nonzero principal factor. -/
theorem invFrac_exists_integral_scaling (M : Model K) (I : InvFrac M) :
    ∃ (a : CoordinateRing M) (J : Ideal (CoordinateRing M)), a ≠ 0 ∧
      (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
        FractionalIdeal.spanSingleton (CoordinateRing M)⁰
          (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ * J := by
  exact FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))

end

end MazurProof.SexticMumford
