import geometry.V2AnalyticGeometry
import RHZeroFreeExtension.V2Conditional
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import RHZeroFreeExtension.analytic_high.V2FinalFixedHigh
import RHZeroFreeExtension.ActualPrimitiveContinuation


noncomputable section
open scoped Classical
open Filter

namespace RHZeroFreeExtension.AnalyticHigh.V2
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem chosen_data_height {Δ:ℝ}(D:HighData Δ)(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(J:ℝ)(hJ:0 ≤ J)
    (hbound: ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))):
     ∃ τ:ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η:Character, ∃ C:ℝ,0 < C  ∧   ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)):=by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice J hJ
  have htau1:τ ≤ 1:=by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith))

theorem physical_probe_estimates_of_chosen_moments (hmom : ChosenMomentInput) :
    RHV2.PhysicalProbeEstimates := by
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩ := hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-RHV2.boundary)/2
  have hloss : 0 < loss := by dsimp [loss];linarith
  have hlossgap : loss < HeckeZeroSupremum.beta-RHV2.boundary := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η _hprimitive
  obtain ⟨hmask,_hOldAnalytic,_hOldBound⟩ :=
    ProbeFinalAssembly.actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    (-(4+RHV2.b)/6),hmask,?_,?_,?_,?_⟩
  · exact RHV2.source_analytic F.S F.exclusions η
  · exact RHV2.source_contraction F.S F.exclusions η
  · have hexp : (RHV2.boundary : ℝ)+(-(4+RHV2.b)/6)=RHV2.lowExponent := by rw [RHV2.lowExponent_signal];ring
    simpa only [hexp] using F.probe_low loss hloss η
  · obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
    obtain ⟨Cm,hCm,hsource⟩ := hsource η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
    filter_upwards [hhigh,hsource] with Z hh hs
    simpa only [RHV2.signalExponent, sub_eq_add_neg, neg_div] using hh Cm hCm.le hs

theorem beta_le_of_chosen_moments (hmom : ChosenMomentInput) :
    HeckeZeroSupremum.beta ≤ RHV2.boundary :=
  RHV2.beta_star_le_of_probes (physical_probe_estimates_of_chosen_moments hmom)

theorem beta_le_of_fine_moments (hmom : FineMomentInput) :
    HeckeZeroSupremum.beta ≤ (RHV2.boundary:ℝ) :=
  beta_le_of_chosen_moments (chosen_input_of_fine hmom)

end RHZeroFreeExtension.AnalyticHigh.V2
end
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.physical_probe_estimates_of_chosen_moments
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.beta_le_of_fine_moments

namespace RHZeroFreeExtension.AnalyticHigh.V2
/-- Assembly keeps the original headline only as an input needed to construct
the finite-kappa moment family; it is not the improved conclusion. -/
theorem beta_le_of_original_headline_and_fine_moment_construction
    (hOld : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (hconstruct : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ) → FineMomentInput) :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (RHV2.boundary : ℝ) :=
  beta_le_of_fine_moments (hconstruct hOld)
end RHZeroFreeExtension.AnalyticHigh.V2
