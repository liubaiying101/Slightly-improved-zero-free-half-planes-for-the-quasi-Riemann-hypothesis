import RHZeroFreeExtension.analytic_high.PerturbedGlobalCorrection
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison

/-! The actual upstream correction H has the required new-domain analytic and
contraction properties. This does not supply the physical J/error bounds. -/
namespace RHZeroFreeExtension.ActualSourceAnalytic
noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler PrincipalSignalComparison
open RHZeroFreeExtension.AnalyticHigh

theorem source_analytic_at_new_boundary (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) :
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ | (34999/40000 : ℝ) < s.re} := by
  exact perturbed_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6)
    (by norm_num) (by norm_num)

theorem source_contraction_at_new_boundary (S : Finset (Ideal O))
    (hS : SourceExclusions S) (η : Character) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re) :
    ‖sourceCorrection η S s - 1‖ ≤ (1/2 : ℝ) := by
  exact perturbed_globalClosedCorrection_bound η S hS.tail s 1 (1/6)
    hs.le (by norm_num) (by norm_num)

#print axioms source_analytic_at_new_boundary
#print axioms source_contraction_at_new_boundary
end
end RHZeroFreeExtension.ActualSourceAnalytic
