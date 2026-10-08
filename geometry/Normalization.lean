import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

namespace RHNormalization
noncomputable section

theorem physical_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z^(21247/60000 : ℝ) : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-(5003/30000 : ℝ)/6 : ℝ) : ℂ)) * (Z : ℂ)^(s-11/16) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (21247/60000) (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring_nf

#print axioms physical_power_identity
end
end RHNormalization
