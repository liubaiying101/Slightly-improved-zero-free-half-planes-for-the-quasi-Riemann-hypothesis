import geometry.V2AnalyticGeometry
import RHZeroFreeExtension.analytic_high.V2GlobalCorrection
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison

/-! Genuine source Euler correction at the radical v2 boundary. The wider
rational half-plane Re(s)>437/500 retains the original summable prime bound
and source exclusion tail. No analyticity or product contraction is assumed. -/
namespace RHV2
noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler PrincipalSignalComparison
open RHZeroFreeExtension.AnalyticHigh
lemma correction_boundary_lower : (437/500 : ℝ) < boundary := by v2_geometry

theorem source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) :
    AnalyticOnNhd ℂ (sourceCorrection eta S) {z : ℂ | boundary < z.re} := by
  apply (v2_globalClosedCorrection_analytic_x eta S hS.tail 1 (1/6)
    (by norm_num) (by norm_num)).mono
  intro z hz
  exact lt_trans correction_boundary_lower hz

theorem source_contraction (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) (z : ℂ) (hz : boundary < z.re) :
    ‖sourceCorrection eta S z-1‖ ≤ (1/2 : ℝ) :=
  v2_globalClosedCorrection_bound eta S hS.tail z 1 (1/6)
    (by linarith [correction_boundary_lower]) (by norm_num) (by norm_num)

theorem source_nonzero (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) (z : ℂ) (hz : boundary < z.re) :
    sourceCorrection eta S z ≠ 0 := by
  have hb := source_contraction S hS eta z hz
  intro hn
  rw [hn, zero_sub, norm_neg, norm_one] at hb
  norm_num at hb

#print axioms source_analytic
#print axioms source_contraction
#print axioms source_nonzero
end
end RHV2
