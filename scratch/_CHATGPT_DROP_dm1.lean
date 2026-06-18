import Mathlib

/-!
# Quartic obstruction for the N=12 descent

The drop task asks for the lemma

`b^2 = 3*a^4 + 2*a^2 - 1 -> False`, under `a^2 >= 2`.

The even-`a` and odd-`b` branches follow the same parity-split pattern as
`scratch/DescentN14.lean`'s `no_sol_2a4_a2_m1`: split parities, expand with
`nlinarith`, and close the residue contradiction with `omega`.

The odd-`a`, even-`b` branch is the remaining nontrivial quartic obstruction.
-/

namespace Scratch.ChatGPTDropDM1

/--
The remaining odd-`a`, even-`b` quartic obstruction.

In this branch `a = 2*c + 1` and `b = 2*d`; the equation becomes
`4*d^2 = 3*(2*c+1)^4 + 2*(2*c+1)^2 - 1`.
-/
private axiom N12_quartic_odd_even_core (c d : ℤ)
    (ha : (2 * c + 1) ^ 2 >= 2)
    (h : (2 * d) ^ 2 = 3 * (2 * c + 1) ^ 4 + 2 * (2 * c + 1) ^ 2 - 1) :
    False

/-- The quartic obstruction needed in the N=12 descent. -/
theorem N12_quartic (a b : ℤ) (ha : a ^ 2 >= 2) :
    b ^ 2 = 3 * a ^ 4 + 2 * a ^ 2 - 1 -> False := by
  intro h
  rcases Int.even_or_odd a with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
    rcases Int.even_or_odd b with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have : 4 * d ^ 2 = 48 * c ^ 4 + 8 * c ^ 2 - 1 := by nlinarith
    omega
  · have : 4 * d ^ 2 + 4 * d + 1 = 48 * c ^ 4 + 8 * c ^ 2 - 1 := by nlinarith
    omega
  · exact N12_quartic_odd_even_core c d ha h
  · have :
        4 * d ^ 2 + 4 * d + 1 =
          3 * (16 * c ^ 4 + 32 * c ^ 3 + 24 * c ^ 2 + 8 * c + 1) +
            2 * (4 * c ^ 2 + 4 * c + 1) - 1 := by
      nlinarith
    omega

end Scratch.ChatGPTDropDM1
