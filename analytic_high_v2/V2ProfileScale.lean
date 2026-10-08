import RHZeroFreeExtension.analytic_high.V2AdaptiveExponent
namespace RHV2
noncomputable section
lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^x)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^y)^(-a-6*e) =
      Z^((1-y)*a+(4/25)*x-33/50+(16-6*y)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring
#print axioms physical_scale_identity
end
end RHV2
