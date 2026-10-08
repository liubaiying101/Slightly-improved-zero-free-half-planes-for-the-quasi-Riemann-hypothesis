import RHZeroFreeExtension.analytic_high.V2MomentCertificate
import RHZeroFreeExtension.analytic_high.V2FinalChosenData
import RHZeroFreeExtension.ActualOriginalBoundary

/-! Full analytic assembly at the radical v2 geometry. The actual physical
probe estimates are constructed before deriving nonvanishing. No moment,
probe-estimate, or improved-boundary hypothesis is supplied to this entry. -/
namespace RHV2
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open RHZeroFreeExtension.AnalyticHigh.V2

 theorem physical_probe_estimates : PhysicalProbeEstimates :=
  physical_probe_estimates_of_chosen_moments
    (OAI.SevenEighths.V2ProbeFinalAssemblyCertifiedBands.chosen_moments_of_original_headline
      RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths)

 theorem beta_star_le : HeckeZeroSupremum.beta ≤ boundary :=
  beta_star_le_of_probes physical_probe_estimates

 theorem hecke_nonzero (chi : Character) (z : ℂ) (hz : boundary<z.re)
    (hpole : z≠1 ∨ chi.residue≠1) : LFunction chi z≠0 :=
  hecke_nonzero_of_probes physical_probe_estimates chi z hz hpole

 theorem dirichlet_nonzero (q : ℕ) (hq : q≠0) (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : boundary<z.re) (hpole : ¬(chi=1 ∧ z=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi z≠0 :=
  dirichlet_nonzero_of_probes physical_probe_estimates q hq chi z hz hpole

 theorem zeta_nonzero (z : ℂ) (hz : boundary<z.re) (hpole : z≠1) : riemannZeta z≠0 :=
  zeta_nonzero_of_probes physical_probe_estimates z hz hpole

#print axioms physical_probe_estimates
#print axioms beta_star_le
#print axioms hecke_nonzero
#print axioms dirichlet_nonzero
#print axioms zeta_nonzero
end
end RHV2
