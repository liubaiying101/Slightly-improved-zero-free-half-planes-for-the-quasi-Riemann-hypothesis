import RHZeroFreeExtension.V2SourceAnalytic
import RHZeroFreeExtension.analytic_high.V2SignalShift
import RHZeroFreeExtension.analytic_high.V2PhysicalNormalization

namespace RHV2
noncomputable section
open MeasureTheory Complex
open OAI OAI.SevenEighths
open HeckeFamily HeckeSignal HeckeSignalShift Continuation
open RHZeroFreeExtension.AnalyticHigh.V2HeckeSignalShift
def kernel (χ : Character) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) (-((4+b)/6)) Z ((a : ℂ)+t*I)

def kernelEnvelope (a C Z : ℝ) : ℝ :=
  Z^(a-(4+b)/6) * Real.exp ((a-5/6)^2) * ((3/2)*C)

theorem kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | boundary < s.re})
    {a Z : ℝ} (ha : boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (v2_quotient_holomorphic χ H hH ha hβ) (-((4+b)/6)) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : boundary < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := v2_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-((4+b)/6)))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | boundary < s.re})
    (hb : ∀ s : ℂ, boundary < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : boundary < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound χ H hb ha ha2 hC hZ hR))


theorem source_kernel_integrable (S : Finset (Ideal HeckeFamily.O))
    (hS : ProbePhysical.SourceExclusions S) (chi : Character)
    {a Z : ℝ} (ha : boundary<a) (ha2 : a≤2)
    (hbeta : HeckeZeroSupremum.beta<a) (hZ : 0<Z) :
    Integrable (kernel chi (PrincipalSignalComparison.sourceCorrection chi S) a Z) := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound chi a hbeta
  exact kernel_integrable chi (PrincipalSignalComparison.sourceCorrection chi S)
    (source_analytic S hS chi).differentiableOn (source_contraction S hS chi)
    ha ha2 hbeta hC hZ hR

#print axioms source_kernel_integrable
#print axioms kernel_continuous
#print axioms kernel_norm_bound
#print axioms kernel_integrable
end
end RHV2
