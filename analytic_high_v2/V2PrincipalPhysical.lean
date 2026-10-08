import geometry.V2AnalyticGeometry
import OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
import RHZeroFreeExtension.analytic_high.V2PrincipalTransport
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open Complex MeasureTheory
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours ProbePrincipalPhysical
local notation "Id" => Ideal HeckeFamily.O
theorem v2_principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact v2_source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

end
end RHZeroFreeExtension.AnalyticHigh
