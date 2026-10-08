import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import RHZeroFreeExtension.analytic_high.PerturbedFinalFixedHigh
import RHZeroFreeExtension.ActualPrimitiveContinuation


noncomputable section
open scoped Classical
open Filter

namespace RHZeroFreeExtension.AnalyticHigh
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

def ChosenMomentInput:Prop:=
   ∀ _hβ:(34999/40000:ℝ) < HeckeZeroSupremum.beta,
     ∃ D:HighData (HeckeZeroSupremum.beta-34999/40000), ∃ F:SourceData D,
     ∃ counts:CountParameters F.modulus ⊤ D.t,
     ∃ J:ℝ,0 ≤ J  ∧   ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput:Prop:=
   ∀ _hβ:(34999/40000:ℝ) < HeckeZeroSupremum.beta,
     ∃ mesh:ℝ → ℝ,( ∀ t:ℝ,0 < t → 0 < mesh t)  ∧ 
     ∀ D:HighData (HeckeZeroSupremum.beta-34999/40000),( ∀ j,D.ell j ≤ mesh D.t/200) → 
     ∀ F:SourceData D, ∀ counts:CountParameters F.modulus ⊤ D.t,
     ∃ J:ℝ,0 ≤ J  ∧   ∀ η:Character, ∃ C:ℝ,0 < C  ∧ 
       ∀ τ:ℝ,0 < τ → τ ≤ 1 →  ∀ᶠ Z:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h:FineMomentInput):ChosenMomentInput:=by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩:=h hβ
  obtain ⟨D,hD⟩:=exists_high_data_fine (HeckeZeroSupremum.beta-34999/40000) (by linarith) mesh hmesh
  obtain ⟨F⟩:=exists_source_data D
  obtain ⟨counts⟩:=source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

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

theorem beta_le_of_chosen_moments (hmom : ChosenMomentInput) :
    HeckeZeroSupremum.beta ≤ (34999/40000:ℝ) := by
  apply RHZeroFreeExtension.ActualPrimitiveContinuation.beta_le_of_uniform_physical_probes
    (34999/40000) (by norm_num) (by norm_num)
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩ := hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-34999/40000)/2
  have hloss : 0 < loss := by dsimp [loss];linarith
  have hlossgap : loss < HeckeZeroSupremum.beta-34999/40000 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η _hprimitive
  obtain ⟨hmask,_hOldAnalytic,_hOldBound⟩ :=
    ProbeFinalAssembly.actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    (-11/16),hmask,?_,?_,?_,?_⟩
  · exact RHZeroFreeExtension.ActualSourceAnalytic.source_analytic_at_new_boundary F.S F.exclusions η
  · exact RHZeroFreeExtension.ActualSourceAnalytic.source_contraction_at_new_boundary F.S F.exclusions η
  · have hexp : (34999/40000 : ℝ)+(-11/16)=7499/40000 := by norm_num
    simpa only [hexp] using F.probe_low loss hloss η
  · obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
    obtain ⟨Cm,hCm,hsource⟩ := hsource η
    apply isBigO_rpow_of_eventual_norm_bound
    refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
    filter_upwards [hhigh,hsource] with Z hh hs
    simpa only [sub_eq_add_neg, neg_div] using hh Cm hCm.le hs

theorem beta_le_of_fine_moments (hmom : FineMomentInput) :
    HeckeZeroSupremum.beta ≤ (34999/40000:ℝ) :=
  beta_le_of_chosen_moments (chosen_input_of_fine hmom)

end RHZeroFreeExtension.AnalyticHigh
end
#print axioms RHZeroFreeExtension.AnalyticHigh.beta_le_of_fine_moments

namespace RHZeroFreeExtension.AnalyticHigh
/-- Assembly keeps the original headline only as an input needed to construct
the finite-kappa moment family; it is not the improved conclusion. -/
theorem beta_le_of_original_headline_and_fine_moment_construction
    (hOld : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (hconstruct : OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (7/8 : ℝ) → FineMomentInput) :
    OAI.SevenEighths.HeckeZeroSupremum.beta ≤ (34999/40000 : ℝ) :=
  beta_le_of_fine_moments (hconstruct hOld)
end RHZeroFreeExtension.AnalyticHigh
