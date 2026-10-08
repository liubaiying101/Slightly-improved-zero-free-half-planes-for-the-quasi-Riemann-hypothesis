import geometry.V2AnalyticGeometry
namespace RHV2
noncomputable section
def canonicalOffset : ℝ := 7/8-boundary
def sourceSaving : ℝ := y/2-(13/75)*h-canonicalOffset
def smallSaving : ℝ := sourceSaving-1/50
def largeConstant : ℝ := x/2+1+y
lemma transport_geometry : 0 < canonicalOffset ∧ 0 < smallSaving ∧
    h < 9/10 ∧ 4/5 < h ∧ ell < 1 ∧ 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧
    5/6 < boundary ∧ boundary < 7/8 := by
  dsimp only [canonicalOffset, sourceSaving, smallSaving, h, x, y, ell, b, boundary]
  obtain ⟨hl, hu⟩ := s_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
lemma smallSaving_lower : (1/20 : ℝ) ≤ smallSaving := by
  dsimp only [smallSaving, sourceSaving, canonicalOffset, h, x, y, ell, b, boundary]
  obtain ⟨hl, hu⟩ := s_bounds
  linarith only [hl, hu]
end
end RHV2
