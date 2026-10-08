import RHZeroFreeExtension.analytic_high.V2CentralExponent
import RHZeroFreeExtension.analytic_high.PerturbedNonfloorExponent

/-! The actual source adaptive count (Delta=0) at the v2 geometry.
This converts a count into an exponent; it does not assume or prove an
arithmetic row-moment estimate. -/
namespace RHV2
noncomputable section
open OAI.SevenEighths

def mixedPhysicalExponent (a v d row q contour : ℝ) : ℝ :=
  physicalExponent a v row q contour+(d-v)*row

def realLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16-6*y)*e+12*v*e+v*eps*(N+8)+loss+ell*mesh

lemma realLoss_bound (N : ℕ) (v e eps loss mesh : ℝ)
    (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    realLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+ell*mesh := by
  have hy : 1/3≤y := by v2_geometry
  have h1 := mul_le_mul_of_nonneg_right hv he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0≤eps*(N+8) by positivity)
  have h3 := mul_nonneg (show 0≤y-1/3 by linarith) he
  unfold realLoss
  nlinarith

lemma central_class_exponent_identity (N : ℕ)
    (a v d row q e eps loss mesh overhead : ℝ) :
    ((1-y)*a+(4/25)*x-33/50+(16-6*y)*e)+
      (overhead+d*row+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-
        ell*(4/25)+ell*q+ell*mesh) =
      mixedPhysicalExponent a v d row q (17/50)+realLoss N v e eps loss mesh+overhead := by
  unfold mixedPhysicalExponent physicalExponent realLoss
  ring

/-- The actual source count on the balanced branch, with a budget paid
from the contradiction gap. The upper bound on a includes all a≤7/8. -/
theorem adaptive_mixed_saving (N : ℕ)
    (a q epsilon epsilonM slotMesh nu zeta mu v d e eps loss mesh overhead saving beta : ℝ)
    (ha : 1/2<a) (ha' : a≤11/12) (hq : 0≤q) (hq' : q≤(2*a-1)/2)
    (hepsilon : 0≤epsilon) (hepsilonM : 0≤epsilonM) (hslot : 0≤slotMesh) (hnu : 0≤nu)
    (hcount : 159*epsilon+epsilonM+slotMesh+7*nu≤1/32)
    (hzeta : 0≤zeta) (hv : v≤h+zeta) (hv1 : v≤1)
    (hmu : 0≤mu) (hdv : d-v≤mu) (he : 0≤e) (heps : 0≤eps)
    (hbudget : h*(159*epsilon+epsilonM+slotMesh+7*nu)+2*zeta+(3/2)*mu+
      (26*e+(N+8)*eps+loss+ell*mesh)+overhead+saving≤beta-boundary) :
    mixedPhysicalExponent a v d
      (ProbeHighRowFamily.adaptiveRowExponent (2*a-1) q 0 epsilon epsilonM slotMesh nu)
      q (17/50)+realLoss N v e eps loss mesh+overhead≤signalExponent beta-saving := by
  let delta := 2*a-1
  let u := q/delta
  let countLoss := 159*epsilon+epsilonM+slotMesh+7*nu
  have hd0 : 0<delta := by dsimp [delta]; linarith
  have hd1 : delta≤5/6 := by dsimp [delta]; linarith
  have hu0 : 0≤u := div_nonneg hq hd0.le
  have hu1 : u≤1/2 := (div_le_iff₀ hd0).mpr (by dsimp [delta] at *; linarith)
  have hl : 0≤countLoss := by dsimp [countLoss]; positivity
  have hr := RHZeroFreeExtension.AnalyticHigh.count_range delta u countLoss
    hd0.le hd1 hu0 hu1 hl hcount
  have hre : RHGeometry.R delta u=R delta u := rfl
  rw [hre] at hr
  have hslo : 0≤R delta u+countLoss+delta/2-(17/50:ℝ) := by linarith [hr.1]
  have hshi : R delta u+countLoss+delta/2-(17/50:ℝ)≤2 := by linarith [hr.2]
  have hm := balanced_physical_margin delta u (R delta u+countLoss) v (17/50)
    countLoss zeta beta hd0.le hd1 hu0 hu1 le_rfl hzeta hv hslo hshi
  have hmul := mul_le_mul_of_nonneg_right hdv (show 0≤R delta u+countLoss by linarith [hr.1])
  have hmax := mul_le_mul_of_nonneg_left (show R delta u+countLoss≤3/2 by linarith [hr.2]) hmu
  have hloss := realLoss_bound N v e eps loss mesh hv1 he heps
  have haeq : (1+delta)/2=a := by dsimp [delta]; ring
  have hqeq : delta*u=q := mul_div_cancel₀ q hd0.ne'
  rw [haeq,hqeq] at hm
  rw [RHZeroFreeExtension.AnalyticHigh.adaptive_zero_loss]
  change mixedPhysicalExponent a v d
    (if delta≤5/6 then RHGeometry.R delta u+159*epsilon+epsilonM+slotMesh+7*nu
      else 1-delta+78*epsilon+epsilonM) q (17/50)+
      realLoss N v e eps loss mesh+overhead≤signalExponent beta-saving
  rw [ite_eq_left hd1, hre]
  have heq : R delta u+159*epsilon+epsilonM+slotMesh+7*nu =
      R delta u+countLoss := by dsimp only [countLoss]; ring
  rw [heq]
  unfold mixedPhysicalExponent
  dsimp only [countLoss] at hm hmul hmax
  dsimp only [countLoss]
  linarith

#print axioms adaptive_mixed_saving
end
end RHV2
