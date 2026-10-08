import OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
import OAI.NumberTheory.DirichletL.Detector.GlobalHolomorphic
import geometry.V2AnalyticGeometry

set_option linter.unusedVariables false

/-! Actual local Euler formulas on the perturbed x-half-plane.
The proofs use upstream coordinate norm estimates and rational denominator
bounds; no perturbed local bound is assumed. The broad summable17/10 bound
is retained, and the narrower second rectangle has exact decay72599/40000.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler

theorem v2_principalDomain_unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (RHV2.boundary:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(11/5:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(87/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(77/100:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith


lemma v2_principalDomain_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : RHV2.boundary≤ x.re) (hz : 4/25≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem v2_principalDomain_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|RHV2.boundary< x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := v2_principalDomain_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem v2_principalDomain_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : RHV2.boundary≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) {w : ℂ|9/10< w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := v2_principalDomain_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem v2_principalDomain_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : RHV2.boundary≤ x.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedClosed Q A eta v x w z) {z : ℂ|4/25< z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := v2_principalDomain_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


end
end RHZeroFreeExtension.AnalyticHigh

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbePhysical OAI.ActualEisensteinCubic
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma v2_principalDomain_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : RHV2.boundary≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply v2_principalDomain_unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem v2_principalDomain_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : RHV2.boundary≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>v2_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma v2_principalDomain_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : RHV2.boundary≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    v2_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem v2_principalDomain_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|RHV2.boundary< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply v2_principalDomain_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact v2_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem v2_principalDomain_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : RHV2.boundary≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply v2_principalDomain_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact v2_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem v2_principalDomain_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : RHV2.boundary≤ x.re) (hw : 9/10≤ w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply v2_principalDomain_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact v2_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_principalDomain_globalClosedCorrection_analytic_x
