import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import RHZeroFreeExtension.analytic_high.V2SignalBounds
import RHZeroFreeExtension.analytic_high.V2PrincipalSlot
import RHZeroFreeExtension.analytic_high.V2PrincipalDomain
import RHZeroFreeExtension.analytic_high.V2PhysicalNormalization
import RHZeroFreeExtension.analytic_high.V2Kernel
import OAI.NumberTheory.DirichletL.PrincipalSlotEstimate
import OAI.NumberTheory.DirichletL.PrincipalMellinResidues
import OAI.NumberTheory.DirichletL.Hecke.SignalBounds
import OAI.NumberTheory.DirichletL.Detector.SourceExclusions
import OAI.NumberTheory.DirichletL.Detector.CompensationActual
import OAI.NumberTheory.DirichletL.Detector.Basic
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
open OAI OAI.SevenEighths
open PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open ProbePhysical ActualEisensteinCubic CompletedGauss PrincipalMellinResidues

variable {κ ι : Type*}

def v2_actualSlotResidue (eta : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (a Z : ℝ) (S : Finset κ)
    (T : κ → Finset PrimeIdeal) (w : κ → PrimeIdeal → ℝ) : ℂ :=
  RHV2.slotResidue (eta.excludePrimes E hE.prime) (sourceCorrection eta E) a Z S T w
    (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase eta (primaryGenerator p.val)) (fun _ p => idealCoeff eta p.val)

theorem v2_raw_inverse_ae_reciprocal (χ : Character) (a : ℝ) :
    (fun t : ℝ => (LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (HeckeReciprocal.reciprocal_eq_inv χ ?_ ?_).symm
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem v2_raw_quotient_integral_eq (χ : Character) (a : ℝ) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t / LFunction χ ((a : ℂ)+t*I)) =
      ∫ t : ℝ, F t * HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply integral_congr_ae
  filter_upwards [v2_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [div_eq_mul_inv, ht]


structure v2_SlotBounds (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(RHV2.boundary : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

theorem v2_slot_scalar_ne_zero (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : v2_SlotBounds S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem v2_slotRatio_error (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : v2_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : RHV2.boundary ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    v2_weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem v2_slotRatio_bound (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : v2_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : RHV2.boundary ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [v2_slotRatio_error S T w Q A η h hs]

theorem v2_principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := v2_principal_geometric_bounds hQ hη hs
  have hV := one_sub_ne_zero_of_norm_le_half _ hg.1
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hR : 1-coordR Q A s (1/6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    linarith
  have hr := coordR_differentiable Q hQ0 A (1/6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ)^s) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hQ0.ne'))).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1/6) hR hV hD)
    (v2_principal_correction_ne_zero hQ hA hη hs)

theorem v2_slotRatio_continuous_line (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : v2_SlotBounds S T w Q A η P) {a : ℝ} (ha : RHV2.boundary ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (v2_principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio PrincipalSignalComparison.slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

theorem v2_slotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    RHV2.slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-((4+RHV2.b)/6)) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold RHV2.slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [v2_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

theorem v2_kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHV2.boundary < s.re})
    {a Z : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (RHV2.kernel χ H a Z) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hh := gaussianContourIntegrand_differentiableOn
    (V2HeckeSignalShift.v2_quotient_holomorphic χ H hH ha hβ) (-((4+RHV2.b)/6)) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem v2_kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, RHV2.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖RHV2.kernel χ H a Z t‖ ≤ RHV2.kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hq := V2HeckeSignalShift.v2_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold RHV2.kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-((4+RHV2.b)/6)))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold RHV2.kernelEnvelope polynomialGaussian; ring_nf

theorem v2_kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHV2.boundary < s.re})
    (hb : ∀ s : ℂ, RHV2.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (RHV2.kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (RHV2.kernelEnvelope a C Z)).mono'
    (v2_kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (v2_kernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem v2_slotResidue_bound_of_reciprocal_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHV2.boundary < s.re})
    (hb : ∀ s : ℂ, RHV2.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : v2_SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => RHV2.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖RHV2.slotResidue χ H a Z S T w Q A η - signal χ H (-((4+RHV2.b)/6)) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-((4+RHV2.b)/6)) * P^(-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := v2_kernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := v2_slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := v2_slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := v2_slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : RHV2.slotResidue χ H a Z S T w Q A η - signal χ H (-((4+RHV2.b)/6)) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        RHV2.kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [v2_slotResidue_eq_reciprocal,
      V2HeckeSignalBounds.v2_contour_shift_left χ H hH hb (-((4+RHV2.b)/6)) a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, RHV2.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, RHV2.kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change RHV2.kernel χ H a Z t * _ - RHV2.kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(RHV2.boundary : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖RHV2.kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (RHV2.kernelEnvelope a C Z * (slotErrorConstant S * P^(-(RHV2.boundary : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (RHV2.kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(RHV2.boundary : ℝ))) :=
        mul_le_mul (v2_kernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold RHV2.kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (RHV2.kernelEnvelope a C Z * (slotErrorConstant S * P^(-(RHV2.boundary : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold RHV2.kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem v2_exists_slotResidue_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHV2.boundary < s.re})
    (hb : ∀ s : ℂ, RHV2.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), v2_SlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => RHV2.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖RHV2.slotResidue χ H a Z S T w Q A η - signal χ H (-((4+RHV2.b)/6)) Z‖ ≤
          D * Z^(a-((4+RHV2.b)/6)) * P^(-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact v2_slotResidue_bound_of_reciprocal_bound χ H hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem v2_raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => RHV2.kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-(((4+RHV2.b)/6 : ℝ) : ℂ)) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply hi.congr
  filter_upwards [v2_raw_inverse_ae_reciprocal χ a] with t ht
  unfold RHV2.kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

theorem v2_source_double_residue_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      PrincipalSignalComparison.slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ => RHV2.kernel χ (fun s => H s 1 (1/6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(RHV2.x : ℝ)) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hiraw := v2_raw_slot_integrable χ (fun s => H s 1 (1/6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := RHV2.ell))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (RHV2.ell) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (RHV2.normalized_source_double_residue W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

private instance : IsPrincipalIdealRing HeckeFamily.O := IsCyclotomicExtension.Rat.three_pid HeckeFamily.K

theorem v2_idealCoeff_norm_one_of_coprime (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator J)) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime χ.modulus _).mpr (by
      simpa only [Ideal.span_singleton_generator] using hc)
  obtain ⟨u, hu⟩ := hu
  change ‖IdealCharacter.value χ.modulus χ.residue J‖ = 1
  rw [IdealCharacter.value, ite_eq_right hJ, ← hu]
  exact FiniteRayExpansion.norm_char_unit χ.residue u

open ProbePhysical ActualEisensteinCubic CompletedGauss

theorem v2_prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

theorem v2_annularPrimeWeight_nonneg (W : ℝ → ℝ) (hW : ∀ x, 0 ≤ W x)
    (scale : ℝ) (P : PrimeIdeal) : 0 ≤ annularPrimeWeight W scale P :=
  mul_nonneg (hW _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem v2_annularPrimeWeight_norm_lower (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (P : PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : c*scale ≤ (Ideal.absNorm P.val : ℝ) :=
  (le_div_iff₀ hscale).mp (hW _ (left_ne_zero_of_mul hw))

theorem v2_annularPrimeWeight_target_unit (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (η : Character)
    (hthreshold : (Ideal.absNorm η.modulus : ℝ) < c*scale) (P : PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : ‖idealCoeff η P.val‖ = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val := by
    exact_mod_cast hthreshold.trans_le (v2_annularPrimeWeight_norm_lower W c scale hscale hW P hw)
  exact v2_idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (v2_prime_coprime_of_norm_gt η P hN)

theorem v2_sourceCorrection_eq_principal (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) : sourceCorrection η E = principalCorrection η E := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  funext s
  exact source_globalCorrection_principal E hE η s

theorem v2_sourceCorrection_differentiable (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ | RHV2.boundary < s.re} :=
  (v2_principalDomain_globalClosedCorrection_analytic_x η E hE.tail 1 (1/6) (by norm_num) (by norm_num)).differentiableOn

theorem v2_sourceCorrection_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (s : ℂ) (hs : RHV2.boundary < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1/2 :=
  v2_principalDomain_globalClosedCorrection_bound η E hE.tail s 1 (1/6) hs.le (by norm_num) (by norm_num)

theorem v2_actual_principal_slot (η : Character) (P : PrimeIdeal) (s : ℂ) :
    compensatedReplacement (coordV (Ideal.absNorm P.val) (1/6))
      (coordW (Ideal.absNorm P.val) 1 1) (coordD (Ideal.absNorm P.val) (idealCoeff η P.val) 1 s)
      (idealMarkedClosed η P s 1 (1/6))
      (star (idealCoeff η P.val) * (Ideal.absNorm P.val : ℂ)^s)
      ((Ideal.absNorm P.val : ℂ)^(-1 : ℂ)) / idealClosedCorrection η P s 1 (1/6) =
      principalSlot (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) s := rfl

theorem v2_exists_actualSlotResidue_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) {a : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset PrimeIdeal) (w : κ → PrimeIdeal → ℝ) (P Z : ℝ),
      480 ≤ P → 1440 * P^(-(RHV2.boundary : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      ‖v2_actualSlotResidue η E hE a Z S T w -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-((4+RHV2.b)/6)) Z‖ ≤
        D * Z^(a-((4+RHV2.b)/6)) * P^(-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨D, hD, hb⟩ := v2_exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (v2_sourceCorrection_differentiable η E hE) (v2_sourceCorrection_bound η E hE)
    ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro T w P Z hP hsmall hw hnorm hcop hmass hZ
  exact (hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z
    ⟨hP, hsmall, hw, hnorm, fun j hj p hp => actualAPhase_norm_le_one η _,
      fun j hj p hp => v2_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp),
      hmass⟩ hZ).2

open PrincipalMellinResidues

theorem v2_slotMass_active (T : κ → Finset ι) (w : κ → ι → ℝ) :
    slotMass (activePools T w) w = slotMass T w := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  funext j
  simp only [slotMass, activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem v2_slotProduct_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    PrincipalSignalComparison.slotProduct S (activePools T w) w Q A η s = PrincipalSignalComparison.slotProduct S T w Q A η s := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply Finset.prod_congr rfl
  intro j hj
  simp only [activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem v2_slotRatio_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotRatio S (activePools T w) w Q A η s = slotRatio S T w Q A η s := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [slotRatio, slotRatio, v2_slotProduct_active, v2_slotMass_active]

theorem v2_slotResidue_active (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    RHV2.slotResidue χ H a Z S (activePools T w) w Q A η = RHV2.slotResidue χ H a Z S T w Q A η := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp only [RHV2.slotResidue, v2_slotRatio_active]

theorem v2_slotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (RHV2.boundary)*ell)
    (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHV2.boundary < s.re})
    (hb : ∀ s : ℂ, RHV2.boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset ι) (w Q : ℝ → κ → ι → ℝ) (A η : ℝ → κ → ι → ℂ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      v2_SlotBounds S (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z) (c0*Z^ell)) :
    (fun Z : ℝ => RHV2.slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
        signal χ H (-((4+RHV2.b)/6)) Z) =O[atTop] (fun Z : ℝ => Z^(a-((4+RHV2.b)/6)-saving)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨D, hD, hd⟩ := v2_exists_slotResidue_bound χ H hH hb ha ha2 hβ S
  apply IsBigO.of_bound (D*c0^(-(RHV2.boundary : ℝ)))
  filter_upwards [hdata, eventually_ge_atTop (1 : ℝ)] with Z hz hZ
  have hZ0 : 0 < Z := by linarith
  have he := (hd (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z)
    (c0*Z^ell) Z hz hZ).2
  rw [v2_slotResidue_active] at he
  have hp : (c0*Z^ell)^(-(RHV2.boundary : ℝ)) = c0^(-(RHV2.boundary : ℝ))*Z^(ell*(-(RHV2.boundary : ℝ))) := by
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  rw [hp] at he
  have hpow : Z^(a-((4+RHV2.b)/6)+ell*(-(RHV2.boundary : ℝ))) ≤ Z^(a-((4+RHV2.b)/6)-saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have he' : ‖RHV2.slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
      signal χ H (-((4+RHV2.b)/6)) Z‖ ≤ (D*c0^(-(RHV2.boundary : ℝ)))*Z^(a-((4+RHV2.b)/6)-saving) := by
    calc
      _ ≤ D*Z^(a-((4+RHV2.b)/6))*(c0^(-(RHV2.boundary : ℝ))*Z^(ell*(-(RHV2.boundary : ℝ)))) := he
      _ = (D*c0^(-(RHV2.boundary : ℝ)))*Z^(a-((4+RHV2.b)/6)+ell*(-(RHV2.boundary : ℝ))) := by
        rw [Real.rpow_add hZ0]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ0 _)] using he'

theorem v2_actualSlotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (RHV2.boundary)*ell)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset PrimeIdeal) (w : ℝ → κ → PrimeIdeal → ℝ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      v2_SlotBounds S (activePools (T Z) (w Z)) (w Z) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
        (c0*Z^ell)) :
    (fun Z : ℝ => v2_actualSlotResidue η E hE a Z S (T Z) (w Z) -
        signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-((4+RHV2.b)/6)) Z)
      =O[atTop] (fun Z : ℝ => Z^(a-((4+RHV2.b)/6)-saving)) :=
  v2_slotResidue_isBigO S c0 ell saving hc0 hsaving (η.excludePrimes E hE.prime)
    (sourceCorrection η E) (v2_sourceCorrection_differentiable η E hE)
    (v2_sourceCorrection_bound η E hE) ha ha2 hβ T w
    (fun _ _ p => Ideal.absNorm p.val)
    (fun _ _ p => actualAPhase η (primaryGenerator p.val)) (fun _ _ p => idealCoeff η p.val) hdata

theorem v2_fixedPrincipal_product_eq (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    fixedPrincipal (∏ p ∈ E, p) = fixedSourcePrincipal E hE.prime := rfl

theorem v2_exists_normalized_actual_source_bound (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : RHV2.boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset PrimeIdeal)
      (w : κ → PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(RHV2.boundary : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = PrincipalSignalComparison.slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (RHV2.ell) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^(RHV2.x : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(RHV2.x : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-((4+RHV2.b)/6)) Z‖ ≤
        D * Z^(a-((4+RHV2.b)/6)) * P^(-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := v2_exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (v2_sourceCorrection_differentiable η E hE) (v2_sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := RHV2.sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : v2_SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => v2_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact v2_source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_exists_normalized_actual_source_bound
#print axioms RHZeroFreeExtension.AnalyticHigh.v2_actualSlotResidue_isBigO
