module

public import scratch.WardSomos

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The Somos-4 numerator `N_n` and denominator `D_n`; `N_n / D_n` is the conserved quantity. -/
@[expose] public def Nseq (b c d : R) (n : ℤ) : R :=
  normEDS b c d (n+2) * normEDS b c d (n-1)^2
    + normEDS b c d (n+1)^2 * normEDS b c d (n-2) + b^2 * normEDS b c d n ^ 3

@[expose] public def Dseq (b c d : R) (n : ℤ) : R :=
  normEDS b c d (n+1) * normEDS b c d n * normEDS b c d (n-1)

/-- Conservation step: `N_{n+1} D_n = N_n D_{n+1}`, a finite `linear_combination` of the adjacent
Somos at `n` and `n+1` (cofactors from sympy Gröbner, remainder 0). -/
public lemma normEDS_conservation (b c d : R) (n : ℤ) :
    Nseq b c d (n+1) * Dseq b c d n = Nseq b c d n * Dseq b c d (n+1) := by
  have s0 := normEDS_adjacent_somos b c d n
  have s1 := normEDS_adjacent_somos b c d (n+1)
  simp only [show (n+1)+2 = n+3 by ring, show (n+1)-2 = n-1 by ring,
    show (n+1)+1 = n+2 by ring, show (n+1)-1 = n by ring] at s1 ⊢
  unfold Nseq Dseq
  simp only [show (n+1)+2 = n+3 by ring, show (n+1)-1 = n by ring,
    show (n+1)+1 = n+2 by ring, show (n+1)-2 = n-1 by ring]
  linear_combination
    (- normEDS b c d n * normEDS b c d (n+1)^3) * s0
    + (normEDS b c d n ^ 3 * normEDS b c d (n+1)) * s1

end FLT.EDS
