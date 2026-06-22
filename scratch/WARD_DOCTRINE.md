# DOCTRINE — close normEDS_adjacent_somos (unlocks the Mazur keystone)

## Goal (one sentence)
Make scratch/WardSomos.lean 0-sorry by closing the 2 recurrence-step certificates
(adjRelRecSteps.even L61, .odd L64) + the routine base case adjRel_four (L37); this
proves the adjacent Somos relation = the keystone EDS core (Ward (m,2,1) instance).

## Avenues (ranked)
(a) Harvest ChatGPT (dm1/dm4) cofactors for the even/odd `linear_combination`, paste + build.
(b) `polyrith` on the even/odd steps — auto-search the linear combination of h1..h5 (Sage backend).
(c) Direct: rewrite normEDS at the doubled index via normEDS_even/odd, set up the cofactor linear
    system, compute via a local CAS/python-sympy script, paste the linear_combination.
(d) `linear_combination` with structural cofactors guessed from the EDS recurrence shape; nlinarith.
(e) Fallback: reroute the Somos proof through Mathlib complEDS / normEDS_mul_complEDS₂ (the doubling
    identity is normEDS(2k)=normEDS(k)·complEDS₂(k)), deriving the adjacent relation differently.
(f) adjRel_four: compute normEDS 6 from normEDS_even 3 (handle the b-factor) + linear_combination.

## Terminal conditions
success = WardSomos.lean builds 0 sorry/0 axiom. Avenue fails = the specific tactic errors with a
documented reason (paste the residual). Then next avenue. Do not stop at "hard".

## Fallback if all fail
Keep the skeleton (526f48b) as the precise named seam; the keystone = these 2 cofactor certificates.
