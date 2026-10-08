import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount
import RHZeroFreeExtension.analytic_high.PerturbedCentralExponent
import geometry.CountOptimization

/-! Fixed-Delta actual source adaptive count exponents and the new physical
mixed exponent. No row energy or improved count conclusion is a premise. -/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI.SevenEighths
open PerturbedCentralExponent

lemma source_balanced_count_eq (δ x : ℝ) :
    Endpoint.balancedRowCount δ (1/2-x) = RHGeometry.R δ x := by
  have hD : Endpoint.denominator (1/2-x)=RHGeometry.D x := by
    rw [← HeckeDetectorRowCount.denominator_endpoint]
    rfl
  have hP : Endpoint.primeWeight (1/2-x)=RHGeometry.P x := by
    rw [← HeckeDetectorRowCount.primeWeight_endpoint]
    rfl
  have hJ : Endpoint.balanceDenominator δ (1/2-x)=RHGeometry.J δ x := by
    unfold Endpoint.balanceDenominator RHGeometry.J
    rw [hD,hP]
  unfold Endpoint.balancedRowCount Endpoint.balancedCutoff RHGeometry.R
  rw [hP,hJ]
  ring

lemma adaptive_zero_loss (δ q ε εm slotMesh ν : ℝ) :
    ProbeHighRowFamily.adaptiveRowExponent δ q 0 ε εm slotMesh ν =
      if δ≤5/6 then RHGeometry.R δ (q/δ)+159*ε+εm+slotMesh+7*ν
      else 1-δ+78*ε+εm := by
  unfold ProbeHighRowFamily.adaptiveRowExponent
  rw [source_balanced_count_eq]
  simp only [zero_div,add_zero]

lemma count_range (δ x loss : ℝ) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hl : 0≤loss) (hl' : loss≤1/32) :
    1-δ≤RHGeometry.R δ x+loss ∧ RHGeometry.R δ x+loss≤139/96 := by
  have ht := RHCount.t_range δ x hδ hδ' hx hx'
  have he : RHGeometry.R δ x=1-δ+(5/6-δ)*(RHCount.t δ x-1) := by
    unfold RHGeometry.R RHCount.t
    change 1-δ+(5/6-δ)*δ*RHCount.P x/(2*RHCount.J δ x) =
      1-δ+(5/6-δ)*(1+δ*RHCount.P x/(2*RHCount.J δ x)-1)
    ring
  have hp := mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤RHCount.t δ x-1 by linarith)
  have hu := mul_le_mul_of_nonneg_left ht.2 (show 0≤5/6-δ by linarith)
  rw [he]
  constructor <;> nlinarith

def mixedPhysicalExponent (a v d R q s : ℝ) : ℝ :=
  physicalExponent a v R q s+(d-v)*R

lemma mixed_physical_slack (a v d R q s μ Rmax : ℝ)
    (hR : 0≤R) (hRmax : R≤Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedPhysicalExponent a v d R q s≤physicalExponent a v R q s+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedPhysicalExponent
  linarith

lemma balanced_mixed_physical_saving (δ x loss ζ μ v d overhead saving : ℝ)
    (hδ : 0≤δ) (hδ' : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hl : 0≤loss) (hl' : loss≤1/32) (hζ : 0≤ζ) (hv : v≤h+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : h*loss+2*ζ+(3/2)*μ+overhead+saving≤19/320000) :
    mixedPhysicalExponent ((1+δ)/2) v d (RHGeometry.R δ x+loss) (δ*x) (17/50)+overhead ≤
      boundary-11/16-saving := by
  have hr := count_range δ x loss hδ hδ' hx hx' hl hl'
  have hslo : 0≤RHGeometry.R δ x+loss+δ/2-(17/50:ℝ) := by linarith [hr.1]
  have hshi : RHGeometry.R δ x+loss+δ/2-(17/50:ℝ)≤2 := by linarith [hr.2]
  have hm := balanced_physical_margin δ x (RHGeometry.R δ x+loss) v (17/50) loss ζ
    hδ hδ' hx hx' le_rfl hζ hv hslo hshi
  have hs := mixed_physical_slack ((1+δ)/2) v d (RHGeometry.R δ x+loss) (δ*x) (17/50) μ (3/2)
    (by linarith [hr.1]) (by linarith [hr.2]) hμ hdv
  linarith

lemma high_mixed_physical_saving (δ q loss ζ μ v d overhead saving : ℝ)
    (hδ : 5/6≤δ) (hδ' : δ≤1) (hq : q≤δ/2)
    (hl : 0≤loss) (hl' : loss≤1/32) (hζ : 0≤ζ) (hv : v≤h+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : h*loss+2*ζ+μ+overhead+saving≤1/20) :
    mixedPhysicalExponent ((1+δ)/2) v d (1-δ+loss) q (17/50)+overhead≤
      boundary-11/16-saving := by
  have hslo : 0≤(1-δ+loss)+δ/2-(17/50:ℝ) := by linarith
  have hshi : (1-δ+loss)+δ/2-(17/50:ℝ)≤2 := by linarith
  have hm := high_physical_margin δ (1-δ+loss) v q (17/50) loss ζ
    hδ hq le_rfl hζ hv hslo hshi
  have hs := mixed_physical_slack ((1+δ)/2) v d (1-δ+loss) q (17/50) μ 1
    (by linarith) (by linarith) hμ hdv
  linarith

def perturbedRealLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (131253/10000)*e+12*v*e+v*eps*(N+8)+loss+ell*mesh

lemma perturbed_realLoss_bound (N : ℕ) (v e eps loss mesh : ℝ)
    (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    perturbedRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+ell*mesh := by
  have h1 := mul_le_mul_of_nonneg_right hv he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0≤eps*(N+8) by positivity)
  unfold perturbedRealLoss
  nlinarith

lemma perturbed_central_class_exponent_identity (N : ℕ)
    (a v d R q e eps loss mesh overhead : ℝ) :
    ((31253/60000)*a-226253/375000+(131253/10000)*e)+
      (overhead+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-
        5003/187500+ell*q+ell*mesh) =
      mixedPhysicalExponent a v d R q (17/50)+perturbedRealLoss N v e eps loss mesh+overhead := by
  unfold mixedPhysicalExponent physicalExponent perturbedRealLoss lx ly ell
  ring

/-- Actual adaptive source exponent at Delta=0; the actual Moments
premises still have to be established for the physical batch. -/
theorem perturbed_adaptive_mixed_saving (N : ℕ)
    (a q ε εm slotMesh ν ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1/2<a) (ha' : a≤1) (hq : 0≤q) (hq' : q≤(2*a-1)/2)
    (hε : 0≤ε) (hεm : 0≤εm) (hslot : 0≤slotMesh) (hν : 0≤ν)
    (hcount : 159*ε+εm+slotMesh+7*ν≤1/32)
    (hζ : 0≤ζ) (hζ' : ζ≤1/48) (hv : v≤h+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ) (he : 0≤e) (heps : 0≤eps)
    (hbudget : h*(159*ε+εm+slotMesh+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+ell*mesh)+overhead+saving≤19/320000) :
    mixedPhysicalExponent a v d
      (ProbeHighRowFamily.adaptiveRowExponent (2*a-1) q 0 ε εm slotMesh ν) q (17/50)+
      perturbedRealLoss N v e eps loss mesh+overhead≤boundary-11/16-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hx : 0≤q/(2*a-1) := div_nonneg hq hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0≤159*ε+εm+slotMesh+7*ν := by positivity
  have haeq : (1+(2*a-1))/2=a := by ring
  have hqeq : (2*a-1)*(q/(2*a-1))=q := mul_div_cancel₀ q hδ.ne'
  have hr := perturbed_realLoss_bound N v e eps loss mesh
    (by unfold h at hv; linarith) he heps
  by_cases hd : 2*a-1≤5/6
  · have hb := balanced_mixed_physical_saving (2*a-1) (q/(2*a-1))
      (159*ε+εm+slotMesh+7*ν) ζ μ v d
      (perturbedRealLoss N v e eps loss mesh+overhead) saving
      hδ.le hd hx hx' hl hcount hζ hv hμ hdv (by linarith)
    rw [haeq,hqeq] at hb
    rw [adaptive_zero_loss]
    simp only [ite_eq_left hd]
    simpa only [add_assoc] using hb
  · have hhl : 0≤78*ε+εm := by positivity
    have hhl' : 78*ε+εm≤1/32 := by linarith
    have hdiff := mul_nonneg (by norm_num [h] : 0≤h)
      (show 0≤(159*ε+εm+slotMesh+7*ν)-(78*ε+εm) by linarith)
    have hh := high_mixed_physical_saving (2*a-1) q (78*ε+εm) ζ μ v d
      (perturbedRealLoss N v e eps loss mesh+overhead) saving
      (le_of_lt (lt_of_not_ge hd)) (by linarith) hq' hhl hhl' hζ hv hμ hdv (by nlinarith)
    rw [haeq] at hh
    rw [adaptive_zero_loss]
    simpa only [ite_eq_right hd,add_assoc] using hh

#print axioms balanced_mixed_physical_saving
#print axioms high_mixed_physical_saving
#print axioms perturbed_adaptive_mixed_saving
end
end RHZeroFreeExtension.AnalyticHigh
