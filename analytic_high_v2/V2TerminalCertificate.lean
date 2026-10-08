import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import RHZeroFreeExtension.analytic_high.V2FinalData

namespace RHZeroFreeExtension.AnalyticHigh.V2
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open OAI OAI.SevenEighths
open CenteredMomentEnergyCertifiedExistence CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyCappedWidthInduction

/-- The original moment induction is specialized at fixed kappa=3/4.  The
original Hecke headline is an explicit premise, not the improved conclusion. -/
theorem fixed_kappa_terminal_certificate {gap : ℝ} (D : HighData gap)
    (F : SourceData D) (hOld : HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (hBeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (bPhi : ℝ) (hbPhi : 0 < bPhi) :
    CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
      2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 (3/4) (D.t/4)
      (count 2 (D.t/4)) := by
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 (3/4) (D.t/4)
  · norm_num
  · intro x hx
    have hh : x ∈ Function.support (F.W : ℝ → ℂ) := by
      change conj (F.W x) ≠ 0 at hx
      change F.W x ≠ 0
      intro hz
      exact hx (by rw [hz]; simp)
    exact F.complex_support hh
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbPhi
  · norm_num
  · norm_num
  · norm_num
  · exact div_pos D.t_pos (by norm_num)
  · exact hBeta
  · linarith

end
end RHZeroFreeExtension.AnalyticHigh.V2
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.fixed_kappa_terminal_certificate
