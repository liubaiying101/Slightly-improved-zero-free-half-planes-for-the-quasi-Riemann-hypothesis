import RHZeroFreeExtension.moment_adapters.FinalAssemblyCertifiedBands
import RHZeroFreeExtension.moment_adapters.DetectorPlainSlotProfile
import RHZeroFreeExtension.ActualOriginalBoundary
import RHZeroFreeExtension.ActualDirichletTransfer
import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

/-! Actual finite-depth moment construction, using only the imported original
seven-eighths theorem to set kappa=3/4. The improved boundary is a conclusion,
not a supplied moment or nonvanishing contract. The conclusion concerns the
actual finite-residue Hecke family over the Eisenstein field. -/
set_option linter.unusedVariables false
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open OAI OAI.SevenEighths
open HeckeFamily HeckeZeroSupremum
open PerturbedProbeFinalAssemblyCertifiedBands
open PerturbedCenteredMomentDetectorPlainMomentParameters
open PerturbedCenteredMomentDetectorPlainSlotProfile

/-- Construct the actual terminal band from the generic source induction. -/
theorem actual_detector_certified_bands : DetectorCertifiedBands := by
  intro hβ D _hfine F bΦ hbΦ
  have hp := fixed_parameters D
  have hOld := RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths
  apply CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
    (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

/-- The FineMomentInput is proved by actual source terminal certificates. -/
theorem actual_fine_moment_input : FineMomentInput :=
  fine_moments_of_certified actual_detector_certified_bands

/-- Actual improved supremum bound for the finite-residue Hecke family; no extension contract is
assumed. Depends on the original paper's fully proved imported headline. -/
theorem actual_beta_le_new_boundary : beta ≤ (34999/40000 : ℝ) :=
  beta_le_of_fine_moments actual_fine_moment_input

theorem actual_hecke_nonzero (χ : Character) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ (actual_beta_le_new_boundary.trans_lt hs) hpole

theorem actual_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  apply RHZeroFreeExtension.ActualDirichletTransfer.dirichlet_nonzero_of_hecke_bound
    (34999/40000) (by norm_num) ?_ q χ s hs hexc
  intro η z hz hp
  exact actual_hecke_nonzero η z hz hp

theorem actual_zeta_nonzero (s : ℂ) (hs : (34999/40000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  apply RHZeroFreeExtension.ActualDirichletTransfer.zeta_nonzero_of_hecke_bound
    (34999/40000) (by norm_num) ?_ s hs
  intro η z hz hp
  exact actual_hecke_nonzero η z hz hp

#print axioms actual_detector_certified_bands
#print axioms actual_fine_moment_input
#print axioms actual_beta_le_new_boundary
#print axioms actual_hecke_nonzero
#print axioms actual_dirichlet_nonzero
#print axioms actual_zeta_nonzero
end
end RHZeroFreeExtension.AnalyticHigh
