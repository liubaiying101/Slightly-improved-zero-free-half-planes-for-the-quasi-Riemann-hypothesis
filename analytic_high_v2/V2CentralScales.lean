import RHZeroFreeExtension.analytic_high.V2AdaptiveExponent
import RHZeroFreeExtension.analytic_high.V2ProfileScale
namespace RHV2
noncomputable section
def sourceExponent (a d row q : ℝ) : ℝ := physicalExponent a d row q (17/50)
lemma floor_source_margin (q zeta d : ℝ) (hq : q≤1/100)
    (hzeta : 0≤zeta) (hd : d≤h+zeta) :
    sourceExponent (51/100) d 1 q-lowExponent≤-(1/200)+2*zeta := by
  have hm := mul_le_mul_of_nonneg_left hq analytic_geometry.1.le
  have hbase : sourceExponent (51/100) h 1 (1/100)-lowExponent≤-(1/200) := by
    dsimp only [sourceExponent,physicalExponent]
    v2_geometry
  have h1 : d-h≤zeta := by linarith
  have hh := mul_le_mul_of_nonneg_right h1 (show (0:ℝ)≤67/100 by norm_num)
  have hz := mul_le_mul_of_nonneg_left (show (67/100:ℝ)≤2 by norm_num) hzeta
  have hi : sourceExponent (51/100) d 1 q=
      sourceExponent (51/100) h 1 (1/100)+(d-h)*(67/100)+ell*(q-1/100) := by
    unfold sourceExponent physicalExponent
    ring
  linarith
#print axioms floor_source_margin
end
end RHV2
