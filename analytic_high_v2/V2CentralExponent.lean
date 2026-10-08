import geometry.V2AnalyticGeometry
/-! Literal physical Mellin exponent at v2 geometry. The actual high
row sums remain separate. The contradiction gap, rather than a fixed
negative ideal endpoint, pays for rounding, contour and height losses. -/
namespace RHV2
noncomputable section
def physicalExponent (a d rowExponent q s : ℝ) : ℝ :=
  x*(1/2-s)+a+s-1-a*y-d*s+d*rowExponent+d*(a-1/2)+ell*(s-1/2+q)

def signalExponent (beta : ℝ) : ℝ := beta-(4+b)/6

lemma physical_endpoint_identity (delta u row s : ℝ) :
    physicalExponent ((1+delta)/2) h row (delta*u) s-lowExponent =
      E delta u+h*(row-R delta u) := by
  dsimp only [physicalExponent, lowExponent, E, C0, x, y, h]
  ring

lemma physical_slope_identity (a d row q s : ℝ) :
    physicalExponent a d row q s =
      physicalExponent a h row q s+(d-h)*(row+a-1/2-s) := by
  unfold physicalExponent
  ring

lemma signal_gap_identity (beta : ℝ) :
    signalExponent beta = lowExponent+(beta-boundary) := by
  rw [lowExponent_signal]
  unfold signalExponent
  ring

theorem balanced_physical_margin (delta u row d s loss zeta beta : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 5/6) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hrow : row ≤ R delta u+loss) (hzeta : 0 ≤ zeta) (hd : d ≤ h+zeta)
    (hslo : 0 ≤ row+delta/2-s) (hshi : row+delta/2-s ≤ 2) :
    physicalExponent ((1+delta)/2) d row (delta*u) s-signalExponent beta ≤
      h*loss+2*zeta-(beta-boundary) := by
  have hend := universal_endpoint delta u hd0 hd1 hu0 hu1
  have hh := gate_h_positive
  have hm := mul_le_mul_of_nonneg_left hrow hh.le
  have hext := mul_le_mul_of_nonneg_right (show d-h ≤ zeta by linarith) hslo
  have hz := mul_le_mul_of_nonneg_left hshi hzeta
  have hi := physical_endpoint_identity delta u row s
  have hs := physical_slope_identity ((1+delta)/2) d row (delta*u) s
  have ha : row+(1+delta)/2-1/2-s = row+delta/2-s := by ring
  rw [ha] at hs
  rw [signal_gap_identity]
  nlinarith

theorem balanced_physical_saving (delta u row d s loss zeta beta overhead saving : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 5/6) (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hrow : row ≤ R delta u+loss) (hzeta : 0 ≤ zeta) (hd : d ≤ h+zeta)
    (hslo : 0 ≤ row+delta/2-s) (hshi : row+delta/2-s ≤ 2)
    (hbudget : h*loss+2*zeta+overhead+saving ≤ beta-boundary) :
    physicalExponent ((1+delta)/2) d row (delta*u) s+overhead ≤
      signalExponent beta-saving := by
  have hm := balanced_physical_margin delta u row d s loss zeta beta
    hd0 hd1 hu0 hu1 hrow hzeta hd hslo hshi
  linarith

#print axioms balanced_physical_margin
#print axioms balanced_physical_saving
end
end RHV2
