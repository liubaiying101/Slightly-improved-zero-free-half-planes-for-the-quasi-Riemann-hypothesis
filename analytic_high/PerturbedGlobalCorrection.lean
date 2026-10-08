import RHZeroFreeExtension.analytic_high.PerturbedEulerRegion
import OAI.NumberTheory.DirichletL.Detector.GlobalCorrection

set_option linter.unusedVariables false

/-! The genuine upstream idealClosedCorrection and globalClosedCorrection
on the new half-plane. The original summable prime majorant and original
cutoff are reused because the new local theorem retains the same17/10 decay.
No product bound, analyticity, or perturbed contraction is assumed.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbePhysical OAI.ActualEisensteinCubic
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma perturbed_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply perturbed_unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem perturbed_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma perturbed_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem perturbed_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|34999/40000< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply perturbed_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem perturbed_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 34999/40000≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply perturbed_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem perturbed_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply perturbed_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end
end RHZeroFreeExtension.AnalyticHigh
