import OAI.NumberTheory.DirichletL.Hecke.SignalBounds
import RHZeroFreeExtension.analytic_high.PerturbedSignalShift
import OAI.NumberTheory.DirichletL.Hecke.SignalShift
import OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeSignalBounds
namespace PerturbedHeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

theorem perturbed_contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000< s.re})
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (34999/40000 : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) {x : ℝ} (hx : 1≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact PerturbedHeckeSignalShift.perturbed_contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem perturbed_signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 34999/40000< s.re})
    (hb : ∀ s : ℂ, 34999/40000< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (34999/40000 : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact PerturbedHeckeSignalShift.perturbed_signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end PerturbedHeckeSignalBounds

end

end RHZeroFreeExtension.AnalyticHigh
