import geometry.V2Optimization
import Mathlib.Analysis.SpecialFunctions.Pow.Real
namespace RHV2
noncomputable section
def lowExponent : ℝ := x/2+b/12
def gramExponent : ℝ := x+b/6
lemma analytic_geometry :
    0 < ell ∧ ell < 1/5 ∧ 0 < b ∧ x < y ∧ y < 1 ∧
    0 < lowExponent ∧ 0 < x-b-ell ∧ x+y = 1-ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  dsimp only [ell, b, x, y, lowExponent]
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor
  · linarith
  · ring
lemma lowExponent_signal : lowExponent = boundary-(4+b)/6 := signal_matching
end
end RHV2
macro "v2_geometry" : tactic => `(tactic|
  first
  | (solve | norm_num)
  | (solve | dsimp only [RHV2.x, RHV2.y, RHV2.h, RHV2.ell, RHV2.b,
       RHV2.lowExponent, RHV2.gramExponent, RHV2.boundary]
             obtain ⟨hl, hu⟩ := RHV2.s_bounds
             nlinarith only [hl, hu])
  | (solve | dsimp only [RHV2.x, RHV2.y, RHV2.h, RHV2.ell, RHV2.b,
       RHV2.lowExponent, RHV2.gramExponent, RHV2.boundary]
             ring))
macro "v2_ring" : tactic => `(tactic|
  (dsimp only [RHV2.x, RHV2.y, RHV2.h, RHV2.ell, RHV2.b,
    RHV2.lowExponent, RHV2.gramExponent, RHV2.boundary] <;> ring))
