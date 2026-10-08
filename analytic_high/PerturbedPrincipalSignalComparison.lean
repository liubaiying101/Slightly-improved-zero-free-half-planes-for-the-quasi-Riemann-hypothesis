import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import RHZeroFreeExtension.analytic_high.PerturbedSignalBounds
import RHZeroFreeExtension.analytic_high.PerturbedPrincipalSlot
import RHZeroFreeExtension.analytic_high.PerturbedGlobalCorrection
import RHZeroFreeExtension.analytic_high.PerturbedPhysicalNormalization
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

theorem perturbed_raw_inverse_ae_reciprocal (χ : Character) (a : ℝ) :
    (fun t : ℝ => (LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (HeckeReciprocal.reciprocal_eq_inv χ ?_ ?_).symm
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem perturbed_raw_quotient_integral_eq (χ : Character) (a : ℝ) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t / LFunction χ ((a : ℂ)+t*I)) =
      ∫ t : ℝ, F t * HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I) := by
  apply integral_congr_ae
  filter_upwards [perturbed_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [div_eq_mul_inv, ht]

variable {κ ι : Type*}

structure perturbed_SlotBounds (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(34999/40000 : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

theorem perturbed_slot_scalar_ne_zero (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : perturbed_SlotBounds S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem perturbed_slotRatio_error (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : perturbed_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 34999/40000 ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(34999/40000 : ℝ)) := by
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    perturbed_weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem perturbed_slotRatio_bound (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : perturbed_SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 34999/40000 ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(34999/40000 : ℝ)) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [perturbed_slotRatio_error S T w Q A η h hs]

theorem perturbed_principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 34999/40000 ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := perturbed_principal_geometric_bounds hQ hη hs
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
    (perturbed_principal_correction_ne_zero hQ hA hη hs)

theorem perturbed_slotRatio_continuous_line (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : perturbed_SlotBounds S T w Q A η P) {a : ℝ} (ha : 34999/40000 ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (perturbed_principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

theorem perturbed_slotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [perturbed_raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

theorem perturbed_kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    {a Z : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (PerturbedHeckeSignalShift.perturbed_quotient_holomorphic χ H hH ha hβ) (-11/16) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem perturbed_kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := PerturbedHeckeSignalShift.perturbed_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-11/16))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem perturbed_kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (perturbed_kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (perturbed_kernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem perturbed_slotResidue_bound_of_reciprocal_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : perturbed_SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := perturbed_kernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := perturbed_slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := perturbed_slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := perturbed_slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [perturbed_slotResidue_eq_reciprocal,
      PerturbedHeckeSignalBounds.perturbed_contour_shift_left χ H hH hb (-11/16) a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change kernel χ H a Z t * _ - kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(34999/40000 : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(34999/40000 : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(34999/40000 : ℝ))) :=
        mul_le_mul (perturbed_kernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(34999/40000 : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem perturbed_exists_slotResidue_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), perturbed_SlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
          D * Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact perturbed_slotResidue_bound_of_reciprocal_bound χ H hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem perturbed_raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [perturbed_raw_inverse_ae_reciprocal χ a] with t ht
  unfold kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

private instance : IsPrincipalIdealRing HeckeFamily.O := IsCyclotomicExtension.Rat.three_pid K

theorem perturbed_idealCoeff_norm_one_of_coprime (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
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

theorem perturbed_prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

theorem perturbed_annularPrimeWeight_nonneg (W : ℝ → ℝ) (hW : ∀ x, 0 ≤ W x)
    (scale : ℝ) (P : PrimeIdeal) : 0 ≤ annularPrimeWeight W scale P :=
  mul_nonneg (hW _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem perturbed_annularPrimeWeight_norm_lower (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (P : PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : c*scale ≤ (Ideal.absNorm P.val : ℝ) :=
  (le_div_iff₀ hscale).mp (hW _ (left_ne_zero_of_mul hw))

theorem perturbed_annularPrimeWeight_target_unit (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (η : Character)
    (hthreshold : (Ideal.absNorm η.modulus : ℝ) < c*scale) (P : PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : ‖idealCoeff η P.val‖ = 1 := by
  have hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val := by
    exact_mod_cast hthreshold.trans_le (perturbed_annularPrimeWeight_norm_lower W c scale hscale hW P hw)
  exact perturbed_idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (perturbed_prime_coprime_of_norm_gt η P hN)

theorem perturbed_sourceCorrection_eq_principal (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) : sourceCorrection η E = principalCorrection η E := by
  funext s
  exact source_globalCorrection_principal E hE η s

theorem perturbed_sourceCorrection_differentiable (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ | 34999/40000 < s.re} :=
  (perturbed_globalClosedCorrection_analytic_x η E hE.tail 1 (1/6) (by norm_num) (by norm_num)).differentiableOn

theorem perturbed_sourceCorrection_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (s : ℂ) (hs : 34999/40000 < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1/2 :=
  perturbed_globalClosedCorrection_bound η E hE.tail s 1 (1/6) hs.le (by norm_num) (by norm_num)

theorem perturbed_actual_principal_slot (η : Character) (P : PrimeIdeal) (s : ℂ) :
    compensatedReplacement (coordV (Ideal.absNorm P.val) (1/6))
      (coordW (Ideal.absNorm P.val) 1 1) (coordD (Ideal.absNorm P.val) (idealCoeff η P.val) 1 s)
      (idealMarkedClosed η P s 1 (1/6))
      (star (idealCoeff η P.val) * (Ideal.absNorm P.val : ℂ)^s)
      ((Ideal.absNorm P.val : ℂ)^(-1 : ℂ)) / idealClosedCorrection η P s 1 (1/6) =
      principalSlot (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) s := rfl

theorem perturbed_exists_actualSlotResidue_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset PrimeIdeal) (w : κ → PrimeIdeal → ℝ) (P Z : ℝ),
      480 ≤ P → 1440 * P^(-(34999/40000 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      ‖actualSlotResidue η E hE a Z S T w -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  obtain ⟨D, hD, hb⟩ := perturbed_exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (perturbed_sourceCorrection_differentiable η E hE) (perturbed_sourceCorrection_bound η E hE)
    ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro T w P Z hP hsmall hw hnorm hcop hmass hZ
  exact (hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z
    ⟨hP, hsmall, hw, hnorm, fun j hj p hp => actualAPhase_norm_le_one η _,
      fun j hj p hp => perturbed_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp),
      hmass⟩ hZ).2

open PrincipalMellinResidues

theorem perturbed_slotMass_active (T : κ → Finset ι) (w : κ → ι → ℝ) :
    slotMass (activePools T w) w = slotMass T w := by
  funext j
  simp only [slotMass, activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem perturbed_slotProduct_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotProduct S (activePools T w) w Q A η s = slotProduct S T w Q A η s := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem perturbed_slotRatio_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotRatio S (activePools T w) w Q A η s = slotRatio S T w Q A η s := by
  rw [slotRatio, slotRatio, perturbed_slotProduct_active, perturbed_slotMass_active]

theorem perturbed_slotResidue_active (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S (activePools T w) w Q A η = slotResidue χ H a Z S T w Q A η := by
  simp only [slotResidue, perturbed_slotRatio_active]

theorem perturbed_slotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (34999/40000)*ell)
    (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000 < s.re})
    (hb : ∀ s : ℂ, 34999/40000 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset ι) (w Q : ℝ → κ → ι → ℝ) (A η : ℝ → κ → ι → ℂ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      perturbed_SlotBounds S (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z) (c0*Z^ell)) :
    (fun Z : ℝ => slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
        signal χ H (-11/16) Z) =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) := by
  obtain ⟨D, hD, hd⟩ := perturbed_exists_slotResidue_bound χ H hH hb ha ha2 hβ S
  apply IsBigO.of_bound (D*c0^(-(34999/40000 : ℝ)))
  filter_upwards [hdata, eventually_ge_atTop (1 : ℝ)] with Z hz hZ
  have hZ0 : 0 < Z := by linarith
  have he := (hd (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z)
    (c0*Z^ell) Z hz hZ).2
  rw [perturbed_slotResidue_active] at he
  have hp : (c0*Z^ell)^(-(34999/40000 : ℝ)) = c0^(-(34999/40000 : ℝ))*Z^(ell*(-(34999/40000 : ℝ))) := by
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  rw [hp] at he
  have hpow : Z^(a-11/16+ell*(-(34999/40000 : ℝ))) ≤ Z^(a-11/16-saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have he' : ‖slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
      signal χ H (-11/16) Z‖ ≤ (D*c0^(-(34999/40000 : ℝ)))*Z^(a-11/16-saving) := by
    calc
      _ ≤ D*Z^(a-11/16)*(c0^(-(34999/40000 : ℝ))*Z^(ell*(-(34999/40000 : ℝ)))) := he
      _ = (D*c0^(-(34999/40000 : ℝ)))*Z^(a-11/16+ell*(-(34999/40000 : ℝ))) := by
        rw [Real.rpow_add hZ0]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ0 _)] using he'

theorem perturbed_actualSlotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (34999/40000)*ell)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset PrimeIdeal) (w : ℝ → κ → PrimeIdeal → ℝ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      perturbed_SlotBounds S (activePools (T Z) (w Z)) (w Z) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
        (c0*Z^ell)) :
    (fun Z : ℝ => actualSlotResidue η E hE a Z S (T Z) (w Z) -
        signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z)
      =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) :=
  perturbed_slotResidue_isBigO S c0 ell saving hc0 hsaving (η.excludePrimes E hE.prime)
    (sourceCorrection η E) (perturbed_sourceCorrection_differentiable η E hE)
    (perturbed_sourceCorrection_bound η E hE) ha ha2 hβ T w
    (fun _ _ p => Ideal.absNorm p.val)
    (fun _ _ p => actualAPhase η (primaryGenerator p.val)) (fun _ _ p => idealCoeff η p.val) hdata

theorem perturbed_fixedPrincipal_product_eq (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    fixedPrincipal (∏ p ∈ E, p) = fixedSourcePrincipal E hE.prime := rfl

theorem perturbed_exists_normalized_actual_source_bound (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : 34999/40000 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset PrimeIdeal)
      (w : κ → PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(34999/40000 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (5003/30000) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^(21247/60000 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(21247/60000 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(34999/40000 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := perturbed_exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (perturbed_sourceCorrection_differentiable η E hE) (perturbed_sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := perturbed_sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : perturbed_SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => perturbed_idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact perturbed_source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end

end RHZeroFreeExtension.AnalyticHigh
