import geometry.V2AnalyticGeometry
import OAI.NumberTheory.DirichletL.Hecke.SignalBounds
import RHZeroFreeExtension.analytic_high.V2SignalShift
import OAI.NumberTheory.DirichletL.Hecke.SignalShift
import OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Topology
open MeasureTheory Set Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeSignalBounds
namespace V2HeckeSignalBounds
open HeckeFamily HeckeSignal Continuation

theorem v2_contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHV2.boundary< s.re})
    (hb : ∀ s : ℂ, RHV2.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (RHV2.boundary : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) {x : ℝ} (hx : 1≤ x) :
    signal χ H c x = (1/(2*Real.pi) : ℂ)*
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ)+y*Complex.I) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact V2HeckeSignalShift.v2_contour_shift_left χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs) hx

theorem v2_signal_isBigO_atTop (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | RHV2.boundary< s.re})
    (hb : ∀ s : ℂ, RHV2.boundary< s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : (RHV2.boundary : ℝ)< a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta< a) :
    signal χ H c =O[atTop] (fun x : ℝ => x^(a+c)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hbound⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  exact V2HeckeSignalShift.v2_signal_isBigO_atTop χ H hH hb c a C 2 ha ha2 hβ hC
    (fun s hs _ => hbound s hs)

end V2HeckeSignalBounds

end

end RHZeroFreeExtension.AnalyticHigh
