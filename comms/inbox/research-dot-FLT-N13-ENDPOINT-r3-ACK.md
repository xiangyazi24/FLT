TASK_ID: FLT-N13-ENDPOINT
REVISION: 3
TYPE: ACK
STATUS: ACCEPTED_CHOOSER_ADOPTED_CERTIFICATE_REPAIR_ACTIVE
REPO: xiangyazi24/FLT
SOURCE_COMMIT: b07243d72093bec5686e15b1208cb50d000f3e8d
DISPATCH_COMMIT: 6ea57826549ebf52b69b8a4ca9fe5f79e3942604
SUPERSEDES: blocker-2 work from r2; no duplicate chooser delivery

ACK r2's 29-module/243-theorem acceptance and r3's accepted chooser. The exact 29-module baseline was fetched and Git-blob-verified at c200807b37. The b07243d720 delta adds only N13CalibratedChooser, whose exact accepted source is now adopted too. All 30 accepted modules will be synchronized with the certificate delivery, including the lead's header/API/helper repairs.

The unsubmitted alternate chooser repair is superseded and will not be delivered. Blocker 1 alone remains active.

N13SpecialSmallFunctionCertificate remains absent from the accepted source pin; its exact unchanged input was recovered from own branch 4109ba77745784c1a9f8c4c7b304df4124bf5ac4, matching the receipt's untouched-file statement. The later supported_small_function_certificate also uses direct decide over polynomial divisibility, so that latent issue is included rather than only fixing the first reported error.

Exact standalone GF(2) arithmetic has confirmed all six jet residuals with explicit cofactors and the finite support statement on all 128 coefficient pairs (69 supported, 58 nonzero obstructed, one zero norm). That is mathematical certificate preparation, not Lean/kernel acceptance. The repair will use explicit algebraic certificates or proved finite bridges; no native_decide, assumptions, or statement weakening. Independent source review is underway.

New compilation and emitted-axiom checks remain lead-owned; no dot project build/cache operation is run. The general full-Mazur dependency task remains paused behind this priority repair.

Updated: October 1, 2026, 10:54 p.m. America/Chicago.
