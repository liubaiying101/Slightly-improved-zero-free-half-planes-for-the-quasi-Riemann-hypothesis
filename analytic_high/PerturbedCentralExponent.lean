import geometry.Endpoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Literal generalized physical high-row exponent arithmetic. This is the
source eight-term exponent with independent scales. Actual arithmetic sum
bounds remain separate; no physical energy bound is assumed or concluded. -/
namespace RHZeroFreeExtension.PerturbedCentralExponent
noncomputable section

def ell : ℝ := 5003/30000
def lx : ℝ := 21247/60000
def ly : ℝ := 28747/60000
def h : ℝ := 16253/20000
def boundary : ℝ := 34999/40000

def physicalExponent (a d rowExponent q s : ℝ) : ℝ :=
  lx*(1/2-s)+a+s-1-a*ly-d*s+d*rowExponent+d*(a-1/2)+ell*(s-1/2+q)

lemma physical_scale_endpoint_identity (δ x R s : ℝ) :
    physicalExponent ((1+δ)/2) h R (δ*x) s - (boundary-11/16) =
      RHGeometry.E ell δ x + h*(R-RHGeometry.R δ x) := by
  unfold physicalExponent lx ly h ell boundary RHGeometry.E
  ring

lemma physical_slope_identity (a d R q s : ℝ) :
    physicalExponent a d R q s = physicalExponent a h R q s+(d-h)*(R+a-1/2-s) := by
  unfold physicalExponent
  ring

/-- Insert the actual count exponent only after it is proved. These are
count/slope hypotheses, not a desired high-energy bound. -/
theorem balanced_physical_margin (δ x R d s loss ζ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hR : R ≤ RHGeometry.R δ x+loss)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+δ/2-s) (hshi : R+δ/2-s ≤ 2) :
    physicalExponent ((1+δ)/2) d R (δ*x) s-(boundary-11/16) ≤
      -19/320000+h*loss+2*ζ := by
  have hend := RHGeometry.perturbed_endpoint δ x hδ hδ' hx hx'
  have hrow := mul_le_mul_of_nonneg_left hR (by norm_num [h] : 0 ≤ h)
  have hext := mul_le_mul_of_nonneg_right (show d-h ≤ ζ by linarith) hslo
  have hz := mul_le_mul_of_nonneg_left hshi hζ
  have hid := physical_scale_endpoint_identity δ x R s
  have hslope := physical_slope_identity ((1+δ)/2) d R (δ*x) s
  have hs : R+(1+δ)/2-1/2-s = R+δ/2-s := by ring
  rw [hs] at hslope
  change RHGeometry.E ell δ x ≤ -19/320000 at hend
  nlinarith

/-- Common-loss conversion, independent of any analytic sum. -/
theorem balanced_physical_saving (δ x R d s loss ζ overhead saving : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hR : R ≤ RHGeometry.R δ x+loss)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+δ/2-s) (hshi : R+δ/2-s ≤ 2)
    (hbudget : h*loss+2*ζ+overhead+saving ≤ 19/320000) :
    physicalExponent ((1+δ)/2) d R (δ*x) s+overhead ≤ boundary-11/16-saving := by
  have hm := balanced_physical_margin δ x R d s loss ζ
    hδ hδ' hx hx' hR hζ hd hslo hshi
  linarith

lemma physical_extend (a d R q s ζ : ℝ) (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+a-1/2-s) (hshi : R+a-1/2-s ≤ 2) :
    physicalExponent a d R q s ≤ physicalExponent a h R q s+2*ζ := by
  have h1 := mul_le_mul_of_nonneg_right (show d-h ≤ ζ by linarith) hslo
  have h2 := mul_le_mul_of_nonneg_left hshi hζ
  rw [physical_slope_identity]
  linarith

/-- The delta>5/6 branch uses the unmarked high count, not the balanced
certificate outside its parameter rectangle. -/
theorem high_physical_margin (δ R d q s loss ζ : ℝ)
    (hδ : 5/6 ≤ δ) (hq : q ≤ δ/2) (hR : R ≤ 1-δ+loss)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+δ/2-s) (hshi : R+δ/2-s ≤ 2) :
    physicalExponent ((1+δ)/2) d R q s-(boundary-11/16) ≤
      -1/20+h*loss+2*ζ := by
  have hs : R+(1+δ)/2-1/2-s = R+δ/2-s := by ring
  have he := physical_extend ((1+δ)/2) d R q s ζ hζ hd
    (by simpa only [hs] using hslo) (by simpa only [hs] using hshi)
  unfold physicalExponent lx ly h ell boundary at *
  nlinarith

/-- No zero witness or marked count is assumed on the actual floor. -/
theorem floor_physical_margin (d s q ζ : ℝ) (hq : q ≤ 1/100)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ 1+(51/100:ℝ)-1/2-s)
    (hshi : 1+(51/100:ℝ)-1/2-s ≤ 2) :
    physicalExponent (51/100) d 1 q s-(boundary-11/16) ≤
      -4279/750000+2*ζ := by
  have he := physical_extend (51/100) d 1 q s ζ hζ hd hslo hshi
  unfold physicalExponent lx ly h ell boundary at *
  linarith

/-- The distinct intermediate row range, using its own source exponent. -/
theorem intermediate_physical_margin (δ d q : ℝ)
    (_hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6) (hq : q ≤ δ/2) (hd : d ≤ 1/2) :
    physicalExponent ((1+δ)/2) d (76/75-(2/3)*δ) q (17/50)-(boundary-11/16) ≤
      -59657/18000000 := by
  have hs : 0 ≤ (76/75-(2/3)*δ)+(1+δ)/2-1/2-(17/50:ℝ) := by linarith
  have he := mul_le_mul_of_nonneg_right hd hs
  unfold physicalExponent lx ly ell boundary
  nlinarith

#print axioms balanced_physical_margin
#print axioms balanced_physical_saving
#print axioms high_physical_margin
#print axioms floor_physical_margin
#print axioms intermediate_physical_margin
end
end RHZeroFreeExtension.PerturbedCentralExponent
