import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
import RHZeroFreeExtension.analytic_high.PerturbedNonfloorExponent

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI OAI.SevenEighths
open PerturbedCentralExponent

lemma perturbed_physical_scale_identity (Z a e : ℝ) (hZ : 0< Z) :
    (Z^(21247/60000:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(28747/60000:ℝ))^(-a-6*e)=
      Z^((31253/60000)*a-226253/375000+(131253/10000)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma perturbed_class_profile_exponent_identity (a v d R q e eps loss mesh cost : ℝ) (N : ℕ) :
    ((31253/60000)*a-226253/375000+(131253/10000)*e)+cost+d*R+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-5003/187500+
      (5003/30000)*q+(5003/30000)*mesh =
    mixedPhysicalExponent a v d R q (17/50)+(131253/10000)*e+
      v*(12*e+eps*(N+8))+loss+(5003/30000)*mesh+cost := by
  unfold mixedPhysicalExponent physicalExponent lx ly ell
  ring

end
end RHZeroFreeExtension.AnalyticHigh
