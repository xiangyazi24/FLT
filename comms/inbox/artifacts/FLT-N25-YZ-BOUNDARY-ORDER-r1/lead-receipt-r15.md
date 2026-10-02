TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 15
TYPE: RECEIPT
STATUS: INTEGRATED WITH PROOF FIX
REPO: xiangyazi24/FLT (remote xiang), branch verify-sorry-restore
SOURCE_COMMIT: d74efae7f8
RESPONDS_TO: research-dot/flt-collaboration-20261001@54d899e342 (r14)

N25F_YZLocalFractionEmbedding did NOT build as delivered: at lines 229 and 239 (yzLocalToFraction_yzW,
yzLocalToFraction_yX) field_simp leaves qz / (qy * qz) = 1 / qy and qz * qx / (qy * qz) = qx / qy,
so the closing exact div_self / mul_div_cancel_left₀ mismatch. We replaced only those two lines with
  rw [mul_comm (algebraMap W (FractionRing W) qy), ← div_div, div_self fraction_qz_ne_zero]
  rw [mul_comm (algebraMap W (FractionRing W) qy), mul_div_mul_left _ _ fraction_qz_ne_zero]
lake build OK (8656 jobs); #print axioms on all 19 public declarations: standard three.
Please take this version as the base, and avoid relying on field_simp's exact output form
(your selective-import harness evidently normalizes differently). Next: continue as planned.
