import geometry.V2AnalyticGeometry
import RHZeroFreeExtension.analytic_high.V2FiniteProductX
import OAI.NumberTheory.DirichletL.Detector.PrincipalContours

set_option linter.unusedVariables false

/-! Full actual ordered Mellin-contour, Fubini, and uniform-tail interface
on the perturbed x-domain. All functions, including arithmeticMultiplier and
continuedSourceMultiplier, remain upstream definitions. Domain-dependent
calls are supplied by newly proved bounds; the generic Mellin/Hecke APIs are
reused. The double residue retains the square of the principal residue.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O
local instance : Countable OAI.ActualEisensteinCubic.O := OAI.ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

@[fun_prop] lemma v2_measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0< Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

lemma v2_ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma v2_global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => v2_ideal_correction_measurable η P.val x w z hx hw hz)

lemma v2_local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := v2_ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma v2_slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (v2_local_multiplier_measurable η P x w z hx hw hz)

lemma v2_zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0≤ zBoxAmplitude M Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma v2_fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤ zBoxAmplitude M Bz*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((ξ:ℂ)+t*I) : ℂ).re by simp; linarith [hξ.1])
  have hn : ‖6*((ξ:ℂ)+t*I)+1‖≤ max 6 (6*Bz+1)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hm : (6:ℝ)≤ max 6 (6*Bz+1) := le_max_left _ _
    have hm' : 6*ξ+1≤ max 6 (6*Bz+1) := (by linarith [hξ.2] : 6*ξ+1≤6*Bz+1).trans (le_max_right _ _)
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero,add_zero]
    rw [abs_of_pos (by linarith [hξ.1] : 0<6*ξ+1),abs_mul]
    norm_num
    unfold height
    nlinarith [mul_le_mul_of_nonneg_right hm (abs_nonneg t)]
  have hi : |(6*((ξ:ℂ)+t*I) : ℂ).im|=6*|t| := by simp [abs_mul]
  have ht : (3+6*|t|)^2≤36*height t^2 := by
    have hh : 3+6*|t|≤6*height t := by unfold height; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have hmax : 0≤ max (6:ℝ) (6*Bz+1) := le_trans (by norm_num) (le_max_left _ _)
  have hh := (height_pos t).le
  rw [hi] at hb
  calc
    _ ≤ principalConstant M*‖6*((ξ:ℂ)+t*I)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(max 6 (6*Bz+1)*height t)*(36*height t^2) := by
      gcongr
    _ = _ := by unfold zBoxAmplitude; ring

lemma v2_LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma v2_LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (v2_LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma v2_reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta< a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma v2_LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ≤‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖≤ A) :
    ‖LFunction χ s‖≤ A/δ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _ ≤ A := hA

lemma v2_fixed_principal_w_bound (M : Id) [NeZero M] {cw υ : ℝ} (hcw : 1< cw)
    (hυ : υ∈Icc (19/20 : ℝ) cw) (hυ1 : υ≠1) (t : ℝ) :
    ‖LFunction (fixedPrincipal M) ((υ:ℂ)+t*I)‖≤
      (wAmplitude M cw/|υ-1|)*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h0 : (υ:ℂ)+t*I≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hυ.1]
  have h1 : (υ:ℂ)+t*I≠1 := by intro h; exact hυ1 (by simpa using congrArg Complex.re h)
  have hδ : 0 < |υ-1| := abs_pos.mpr (sub_ne_zero.mpr hυ1)
  have h := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ
    (pole_distance_vertical 1 υ t) (fixed_principal_w_growth M hcw hυ t)
  convert h using 1
  ring

lemma v2_fixed_principal_z_bound (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) (hξ1 : 6*ξ≠1) :
    ‖LFunction (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤
      (zBoxAmplitude M Bz/|6*ξ-1|)*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h0 : (6*((ξ:ℂ)+t*I) : ℂ)≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hξ.1]
  have h1 : (6*((ξ:ℂ)+t*I) : ℂ)≠1 := by intro h; exact hξ1 (by simpa using congrArg Complex.re h)
  have hd : |6*ξ-1|≤‖6*((ξ:ℂ)+t*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+t*I)-1)
  have hδ : 0 < |6*ξ-1| := abs_pos.mpr (sub_ne_zero.mpr hξ1)
  have h := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ hd
    (v2_fixed_principal_z_box_growth M Bz ξ t hξ)
  convert h using 1
  ring

lemma v2_arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma v2_arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hH := v2_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := v2_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (v2_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (v2_LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (v2_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun p : HeightSpace => 6*p.1.2))
  have hZL' : Measurable (fun p : HeightSpace => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+p.1.2*I))) := by
    convert hZL using 1
    funext p
    congr 1
    push_cast
    ring
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma v2_boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0< boxScale X Y Z a Bs Bz cw := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

lemma v2_height_le_joint_s (t v u : ℝ) : height t≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]
lemma v2_height_le_joint_z (t v u : ℝ) : height v≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]
lemma v2_height_le_joint_w (t v u : ℝ) : height u≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

lemma v2_arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0<δw) (hdz : 0<δz)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw≤‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz≤‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1/2-((ξ:ℂ)+p.1.2*I))
    (show (1/2-((ξ:ℂ)+p.1.2*I) : ℂ).re∈Icc (1/2-Bz) (1/2-33/200) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
      norm_num only [show (1/2:ℂ).re=1/2 by norm_num]
      constructor <;> linarith [hξ.1,hξ.2])
  have hz := cpow_le_scaleBound hZ (((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)
    (show ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1) : ℂ).re∈Icc (a+33/200-1) (Bs+Bz-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hσ.1,hσ.2,hξ.1,hξ.2])
  have hy := cpow_le_scaleBound hY (((υ:ℂ)+p.2*I)-1)
    (show (((υ:ℂ)+p.2*I)-1 : ℂ).re∈Icc (19/20-1) (cw-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hυ.1,hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖≤ C*height p.1.1^2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := v2_combined_slot_bound η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
    ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2) (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ:ℂ)+p.2*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hυ.1]
  have hw1 : (υ:ℂ)+p.2*I≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hwgap; linarith
  have hz0 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hξ.1]
  have hz1 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hzgap; linarith
  have hlz0 := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (v2_fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏P∈S,P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏P∈S,P)) (6*((ξ:ℂ)+p.1.2*I))‖≤
      (zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3 := by convert hlz0 using 1; ring
  have hlw : ‖LFunction (fixedPrincipal (∏P∈S,P)) ((υ:ℂ)+p.2*I)‖≤
      (wAmplitude (∏P∈S,P) cw/δw)*height p.2^3 := by convert hlw0 using 1; ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1/2-Bz) (1/2-33/200)).le
  have hsY := (scaleBound_pos Y (19/20-1) (cw-1)).le
  have hsZ := (scaleBound_pos Z (a+33/200-1) (Bs+Bz-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (v2_slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (v2_zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏P∈S,P) hcw).le hdw.le
  calc
    _ = ‖(X:ℂ)^(1/2-((ξ:ℂ)+p.1.2*I))‖ *
        ‖(Z:ℂ)^(((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)‖ *
        ‖(Y:ℂ)^(((υ:ℂ)+p.2*I)-1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖ *
        ‖globalClosedCorrection η S ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          slotMultiplier η J T b ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ := by
      simp only [arithmeticMultiplier,norm_mul]
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*height p.1.1^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*height p.2^3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*jointHeight p.1.1 p.1.2 p.2^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*jointHeight p.1.1 p.1.2 p.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*jointHeight p.1.1 p.1.2 p.2^3) := by
      gcongr <;> first | positivity | exact v2_height_le_joint_s _ _ _ | exact v2_height_le_joint_z _ _ _ | exact v2_height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma v2_arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply v2_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem v2_continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I))
    (v2_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|) 8
    (v2_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall (fun p => v2_arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

lemma v2_outer_height_ne_zero_ae : ∀ᵐp : HeightSpace ∂heightMeasure, p.1.1≠0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hh : ∀ᵐp : ℝ×ℝ ∂volume.prod volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  exact Measure.quasiMeasurePreserving_fst.ae hh

lemma v2_continued_joint_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    (fun p : HeightSpace => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) =ᵐ[heightMeasure]
    (fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
      ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
      (slotMultiplier η J T b ((a:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  filter_upwards [v2_outer_height_ne_zero_ae] with p hp
  apply v2_continued_source_eq_raw
  · intro h; exact hp (by simpa using congrArg Complex.im h)
  · intro h; exact hp (by simpa using congrArg Complex.im h)

theorem v2_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply (v2_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [v2_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem v2_source_joint_fubini {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    ((∫p, F p ∂heightMeasure)=∫t : ℝ,∫v : ℝ,∫u : ℝ,F ((t,v),u)) ∧
    ((∫p, F p ∂heightMeasure)=∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((t,v),u)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  have hi := v2_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

lemma v2_arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1< cw) (hC : 0≤ C) (hw : 0≤δw) (hz : 0≤δz) :
    0≤ arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (v2_boxScale_pos X Y Z a Bs Bz cw).le
  have hb := v2_slotBound_nonneg J T b Bs Bz
  have hza := v2_zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

theorem v2_continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0≤ C ∧ 0< K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume)≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := v2_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := v2_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (v2_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,v2_arithmetic_profile_eq_source] using hh

theorem v2_source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,K,hC,hK,hslice⟩ := v2_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z a (1/6+e) (19/20) 3 hX hY hZ ha hβ
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  have hi := (hslice .s t).1
  have hs0 : (a:ℂ)+t*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hpair : Integrable (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I))
        ((19/20:ℝ)+q.2*I) ((1/6+e:ℝ)+q.1*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((1/6+e:ℝ)+q.1*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((19/20:ℝ)+q.2*I)) (volume.prod volume) := by
    simpa only [sliceMap,v2_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem v2_source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : RHV2.boundary≤ s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0< e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (v2_slotBound_nonneg J T b _ _))
    (v2_zBoxAmplitude_nonneg _ _) 0 3
  · exact (v2_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using v2_combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact v2_fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem v2_source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
    HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
    (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (RHV2.boundary : ℝ)≤(((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := v2_source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (v2_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9/10 : ℝ)< w.re
    linarith [hw.1]
  · intro z hz
    have hh := v2_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith) hη hcw
    convert v2_boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (v2_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num)).mono
    intro z hz
    change (4/25 : ℝ)< z.re
    linarith [hz.1]
  · exact hzb
  · exact v2_source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem v2_source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
    ∀ᵐt : ℝ, let s : ℂ := (a:ℂ)+t*I
      let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s)
      let π := fixedSourcePrincipal S hS.prime
      verticalIntegral (1/6+e) (fun z => verticalIntegral cw
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
      HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
      (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply v2_source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

lemma v2_residue_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s z : ℂ) :
    residueArithmetic η S hS J T b X Z s z*profile W0 W1 s 1 z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s 1 z *
        LFunction (fixedSourcePrincipal S hS) (6*z) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold residueArithmetic profile continuedSourceMultiplier
  simp only [sub_self,Complex.cpow_zero,mul_one]
  ring

lemma v2_residue_arithmetic_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (hβ : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) :
    Measurable (fun q : ℝ×ℝ => residueArithmetic η S hS J T b X Z
      ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hH := v2_global_correction_measurable η S (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := v2_slot_multiplier_measurable η J T b (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (v2_reciprocal_vertical_continuous (η.excludePrimes S hS) a hβ).measurable.comp
    (by fun_prop : Measurable (fun q : ℝ×ℝ => q.1))
  have hL := (v2_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun q : ℝ×ℝ => 6*q.2))
  have hL' : Measurable (fun q : ℝ×ℝ => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+q.2*I))) := by
    convert hL using 1
    funext q
    congr 1
    push_cast
    ring
  unfold residueArithmetic
  fun_prop (disch := aesop)

lemma v2_residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Z a ξ C : ℝ) (hX : 0< X) (hZ : 0< Z) (ha : RHV2.boundary≤ a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (q : ℝ×ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)‖≤
      residueAmplitude S J T b X Z a ξ C*jointHeight q.1 q.2 0^5 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖≤ C*height q.1^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := v2_combined_slot_bound η S hS.tail J T b hT ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := v2_fixed_principal_z_bound (∏P∈S,P) ξ ξ q.2 ⟨hξ,le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1/2-ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a+ξ-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (v2_slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (v2_zBoxAmplitude_nonneg (∏P∈S,P) ξ) (abs_nonneg (6*ξ-1))
  have hq1 := (height_pos q.1).le
  have hq2 := (height_pos q.2).le
  have hqJ := (jointHeight_pos q.1 q.2 0).le
  calc
    _ = X^(1/2-ξ)*Z^(a+ξ-1)*
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖ *
        ‖globalClosedCorrection η S ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
          slotMultiplier η J T b ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ := by
      simp only [residueArithmetic,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      norm_num
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*height q.1^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*height q.2^3) := by
      gcongr
      first | positivity | exact hL
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*jointHeight q.1 q.2 0^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr <;> first | positivity | exact v2_height_le_joint_s _ _ _ | exact v2_height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

lemma v2_residueAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (X Z a ξ C : ℝ)
    (hX : 0≤ X) (hZ : 0≤ Z) (hC : 0≤ C) : 0≤ residueAmplitude S J T b X Z a ξ C := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hb := v2_slotBound_nonneg J T b a ξ
  have hza := v2_zBoxAmplitude_nonneg (∏P∈S,P) ξ
  unfold residueAmplitude
  positivity

theorem v2_continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) 5 0
  have hm := v2_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hb := v2_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (v2_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ×ℝ => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap,onLines,ofReal_one,ofReal_zero,zero_mul,add_zero] using
    v2_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)

theorem v2_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply (v2_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [v2_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem v2_source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hi := v2_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral,integral_const_mul,mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))).const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem v2_residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hi := v2_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem v2_source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  let R := HeckeReciprocal.regularizedL π 1
  let A := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let B := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let D := fun s => R*verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))
  let E := fun s => R^2/6*K s 1 (1/6)
  have hA : Integrable (fun t : ℝ => A ((a:ℂ)+t*I)) :=
    v2_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) cw cw hX hY hZ ha hβ (by linarith) hcw ⟨by linarith,le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a:ℂ)+t*I)) :=
    v2_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) (19/20) cw hX hY hZ ha hβ (by linarith) hcw ⟨le_rfl,by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a:ℂ)+t*I)) :=
    (v2_residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33/200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐt : ℝ,A ((a:ℂ)+t*I)=B ((a:ℂ)+t*I)+D ((a:ℂ)+t*I)+E ((a:ℂ)+t*I) :=
    v2_source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e cw hX hY hZ ha hβ hcw he
  have hE : Integrable (fun t : ℝ => E ((a:ℂ)+t*I)) := by
    apply ((hA.sub hB).sub hD).congr
    filter_upwards [hp] with t ht
    change A ((a:ℂ)+t*I)-B ((a:ℂ)+t*I)-D ((a:ℂ)+t*I)=E ((a:ℂ)+t*I)
    rw [ht]
    ring
  have heq : verticalIntegral a A=verticalIntegral a (fun s => B s+D s+E s) := by
    unfold verticalIntegral
    congr 1
    exact integral_congr_ae hp
  rw [verticalIntegral_add a _ _ (hB.add hD) hE,verticalIntegral_add a _ _ hB hD] at heq
  change verticalIntegral a A=verticalIntegral a B+R*verticalIntegral a _+R^2/6*verticalIntegral a _
  rw [heq]
  simp only [D,E,verticalIntegral,integral_const_mul]
  ring

theorem v2_source_initial_ordered {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral 3 (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral 3 (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simpa only [show (1/6+11/6:ℝ)=2 by norm_num] using
    v2_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z 3 (11/6) 3 hX hY hZ (by v2_geometry)
      (by linarith [HeckeZeroSupremum.beta_le_one]) (by v2_geometry) (by norm_num)

theorem v2_source_uniform_joint_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      6*ξ≠1→υ≠1→∀R : ℝ,0≤ R→
      (∫p : HeightSpace in outsideBox R,
        ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
          (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
          LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| * K/(1+R)^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  obtain ⟨K0,hK0,hm⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ hξ1 hυ1 R hR0
  let A := arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1|
  have hA : 0≤ A := v2_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
    (abs_nonneg _) (abs_nonneg _)
  have hi := v2_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z σ ξ υ cw hX hY hZ (ha.trans hσ.1) (hβ.trans_le hσ.1) hξ.1 hcw hυ hξ1 hυ1
  have hmi := (hm σ hσ ξ hξ υ hυ).1
  have hbound := v2_arithmetic_onLines_bound η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ hξ1 hυ1 hC hR
  have hdom : ∀ᵐp : HeightSpace ∂heightMeasure,
      ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
      A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) := by
    filter_upwards [v2_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ] with p hp
    rw [←hp,←v2_arithmetic_profile_eq_source]
    rw [norm_mul]
    simpa only [mul_assoc,A,onLines] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg (onLines W0 W1 σ ξ υ p))
  calc
    _ ≤ ∫p : HeightSpace in outsideBox R,
        A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure :=
      integral_mono_ae hi.norm.integrableOn (hmi.const_mul A).integrableOn (ae_restrict_of_ae hdom)
    _ = A*(∫p : HeightSpace in outsideBox R,
        jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _ ≤ A*(K/(1+R)^N) := mul_le_mul_of_nonneg_left (hk σ hσ ξ hξ υ hυ R hR0) hA
    _ = _ := by dsimp [A]; ring

lemma v2_LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  classical
  have hm := ((HeckeOrigin.poleRemoved_entire χ).continuous.measurable).div
    (measurable_id.sub_const (1:ℂ))
  have h1 : Measurable (fun s : ℂ => if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (1:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 1)) hm
  have h0 : Measurable (fun s : ℂ => if s=0 then LFunction χ 0 else
      if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (0:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 0)) h1
  convert h0 using 1
  funext s
  split_ifs with hs0 hs1
  · subst s; rfl
  · subst s; rfl
  · exact v2_LFunction_eq_pole_quotient χ hs0 hs1

lemma v2_arithmetic_onLines_measurable_all {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hH := v2_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := v2_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (v2_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (v2_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => (υ:ℂ)+p.2*I))
  have hZL := (v2_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => 6*((ξ:ℂ)+p.1.2*I)))
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma v2_joinWGap_pos (axis : SliceAxis) (υ : ℝ) (hυ : axis≠.w→υ≠1) : 0< joinWGap axis υ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold joinWGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hυ h))
lemma v2_joinZGap_pos (axis : SliceAxis) (ξ : ℝ) (hξ : axis≠.z→6*ξ≠1) : 0< joinZGap axis ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold joinZGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hξ h))

lemma v2_slice_w_gap (axis : SliceAxis) (R υ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinWGap axis υ≤‖((υ:ℂ)+(sliceMap axis R q).2*I)-1‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  cases axis
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using hR.trans (pole_distance_horizontal 1 υ R)
lemma v2_slice_z_gap (axis : SliceAxis) (R ξ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinZGap axis ξ≤‖6*((ξ:ℂ)+(sliceMap axis R q).1.2*I)-1‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  cases axis
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.1*I)-1)
  · have hi : 6*|R|≤‖6*((ξ:ℂ)+R*I)-1‖ := by
      simpa [abs_mul] using Complex.abs_im_le_norm (6*((ξ:ℂ)+R*I)-1)
    simpa [joinZGap,sliceMap] using (by linarith : (6:ℝ)≤6*|R|).trans hi
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.2*I)-1)

theorem v2_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR0
  have hm := v2_arithmetic_onLines_measurable_all η S hS.prime J T b X Y Z σ ξ υ hX hY hZ (hβ.trans_le hσ.1)
  have hb (q : ℝ×ℝ) := v2_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C
    hX hY hZ ha hσ hξ hcw hυ (joinWGap axis υ) (joinZGap axis ξ)
    (v2_joinWGap_pos axis υ hυ1) (v2_joinZGap_pos axis ξ hξ1) hC hR (sliceMap axis R q)
    (v2_slice_w_gap axis R υ hR0 q) (v2_slice_z_gap axis R ξ hR0 q)
  have hh := hk σ hσ ξ hξ υ hυ axis R
    (arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ))
    (v2_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
      (v2_joinWGap_pos axis υ hυ1).le (v2_joinZGap_pos axis ξ hξ1).le)
    (fun q : ℝ×ℝ => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ:ℂ)+(sliceMap axis R q).1.1*I) ((υ:ℂ)+(sliceMap axis R q).2*I)
      ((ξ:ℂ)+(sliceMap axis R q).1.2*I))
    (hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable hb
  simpa only [onLines,v2_arithmetic_profile_eq_source] using hh

theorem v2_residue_uniform_moments {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ residueAmplitude S J T b X Z a ξ C*K := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) (5+N) 0
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  let A := residueAmplitude S J T b X Z a ξ C
  have hA : 0≤ A := v2_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC
  let F : ℝ×ℝ → ℂ := fun q => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) *
    onLines W0 W1 a ξ 1 (sliceMap .w 0 q)
  have hm := v2_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hFc : AEStronglyMeasurable F (volume.prod volume) := hm.aestronglyMeasurable.mul
    (((onLines_continuous W0 W1 a1 b1 ha1 hW1 a ξ 1 (by linarith)).comp
      (sliceMap_continuous .w 0)).aestronglyMeasurable)
  have hb := v2_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hmom := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
  have hdom (q : ℝ×ℝ) : jointHeight q.1 q.2 0^N*‖F q‖≤
      A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ jointHeight q.1 q.2 0^N * ((A*jointHeight q.1 q.2 0^5)*
          ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb q) (norm_nonneg _))
          (pow_nonneg (jointHeight_pos _ _ _).le _)
      _ = _ := by rw [pow_add]; ring
  have hi : Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) := by
    apply (hmom.1.const_mul A).mono'
    · exact (by unfold jointHeight; fun_prop : Continuous (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)).aestronglyMeasurable.mul hFc.norm
    · apply Eventually.of_forall
      intro q
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)),sliceMap] using hdom q
  have hn : (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ A*K := by
    calc
      _ ≤ ∫q : ℝ×ℝ,A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖)
          ∂volume.prod volume := integral_mono hi (hmom.1.const_mul A) hdom
      _ = A*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖
          ∂volume.prod volume) := integral_const_mul _ _
      _ ≤ A*K := mul_le_mul_of_nonneg_left (by simpa only [sliceMap,pow_zero,div_one] using hmom.2) hA
  have heq : F =ᵐ[volume.prod volume] (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    dsimp only [F,onLines,sliceMap]
    simp only [ofReal_one,ofReal_zero,zero_mul,add_zero]
    rw [v2_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z,
      v2_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
  have hweight : (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)=ᵐ[volume.prod volume]
      (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N) := Eventually.of_forall (fun _ => rfl)
  have heqw := hweight.mul (heq.fun_comp (fun z : ℂ => ‖z‖))
  exact ⟨hi.congr heqw, (integral_congr_ae heqw).symm.trans_le hn⟩

lemma v2_residueOutside_measurable (R : ℝ) : MeasurableSet (residueOutside R) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold residueOutside
  measurability

theorem v2_residue_uniform_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,0≤ R→
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤
        residueAmplitude S J T b X Z a ξ C*K/(1+R)^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_residue_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hi,hb⟩ := hk η S hS J T b hT X Y Z hX hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  let F := fun q : ℝ×ℝ =>
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
      (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
  have hF := v2_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  have hdom (q : ℝ×ℝ) (hq : q∈residueOutside R) :
      ‖F q‖≤ jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N := by
    have hh : 1+R≤ jointHeight q.1 q.2 0 := by
      rcases hq with h|h <;> unfold jointHeight <;> simp only [abs_zero,add_zero] <;>
        linarith [abs_nonneg q.1,abs_nonneg q.2]
    have hp := pow_le_pow_left₀ (by linarith : 0≤1+R) hh N
    apply (le_div_iff₀ (pow_pos (by linarith : 0<1+R) N)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (F q))
  change (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤_
  calc
    _ ≤ ∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N
        ∂volume.prod volume := setIntegral_mono_on hF.norm.integrableOn (hi.div_const _).integrableOn
          (v2_residueOutside_measurable R) hdom
    _ = (∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := integral_div _ _
    _ ≤ (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_le_integral hi (Eventually.of_forall (fun q =>
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

lemma v2_continued_high_slice_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ ξ υ : ℝ)
    (axis : SliceAxis) (R : ℝ) (hR : R≠0) :
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,(sliceMap axis R q).1.1≠0 := by
    cases axis
    · exact Eventually.of_forall (fun _ => hR)
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠0 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠1 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  dsimp only
  rw [v2_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma v2_source_axis_gaps {e : ℝ} (he : 0< e) :
    |(19/20:ℝ)-1|=1/20 ∧ |6*(1/6+e)-1|=6*e ∧ |6*(33/200:ℝ)-1|=1/100 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  constructor
  · norm_num
  constructor
  · rw [show 6*(1/6+e)-1=6*e by ring,abs_of_pos (by positivity)]
  · norm_num

theorem v2_raw_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset PrimeIdeal)(b : ι → PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((σ:ℂ)+p.1.1*I) (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I))
        (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs Bz cw ha hβ hcw N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have hh := hc σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have heq := v2_continued_high_slice_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ axis R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_source_uniform_joint_tails

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_residue_uniform_moments

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_raw_source_uniform_high_slices
