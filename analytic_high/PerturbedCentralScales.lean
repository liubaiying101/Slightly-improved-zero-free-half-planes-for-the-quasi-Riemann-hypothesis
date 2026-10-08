import RHZeroFreeExtension.analytic_high.PerturbedCentralExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

namespace RHZeroFreeExtension.PerturbedCentralExponent
noncomputable section

def sourceExponent (a d R q : ℝ) : ℝ := physicalExponent a d R q (17/50)

def realLoss (N : ℕ) (d e eps heightLoss mesh : ℝ) : ℝ :=
  (131253/10000)*e+12*d*e+d*eps*(N+8)+heightLoss+(5003/30000)*mesh

theorem realLoss_bound (N : ℕ) (d e eps heightLoss mesh : ℝ)
    (hd : d ≤ 1) (he : 0 ≤ e) (heps : 0 ≤ eps) :
    realLoss N d e eps heightLoss mesh ≤
      26*e+(N+8)*eps+heightLoss+(5003/30000)*mesh := by
  have h1 := mul_le_mul_of_nonneg_right hd he
  have h2 := mul_le_mul_of_nonneg_right hd (show 0 ≤ eps*(N+8) by positivity)
  unfold realLoss
  nlinarith

theorem physical_scale_identity (Z a e : ℝ) (hZ : 0 < Z) :
    (Z^(21247/60000 : ℝ))^(4/25 : ℝ)*Z^(a+16*e-33/50)*
      (Z^(28747/60000 : ℝ))^(-a-6*e) =
    Z^((31253/60000)*a-226253/375000+(131253/10000)*e) := by
  rw [←Real.rpow_mul hZ.le, ←Real.rpow_mul hZ.le,
    ←Real.rpow_add hZ, ←Real.rpow_add hZ]
  congr 1
  ring

theorem floor_source_margin (q ζ d : ℝ) (hq : q ≤ 1/100)
    (_hζ : 0 ≤ ζ) (hd : d ≤ h+ζ) :
    sourceExponent (51/100) d 1 q-(boundary-11/16) ≤ -1093/192000+2*ζ := by
  unfold sourceExponent physicalExponent h lx ly ell boundary at *
  linarith

theorem intermediate_source_margin (δ q d : ℝ) (_hδ : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hq : q ≤ δ/2) (hd : d ≤ 1/2) :
    sourceExponent ((1+δ)/2) d (76/75-(2/3)*δ) q-(boundary-11/16) ≤
      -59657/18000000 := by
  have hs : 0 ≤ (76/75-(2/3)*δ)+δ/2-17/50 := by linarith
  have hm := mul_le_mul_of_nonneg_right hd hs
  simp only [sourceExponent, physicalExponent, lx, ly, ell, boundary]
  nlinarith

#print axioms physical_scale_identity
#print axioms floor_source_margin
#print axioms intermediate_source_margin
end
end RHZeroFreeExtension.PerturbedCentralExponent
