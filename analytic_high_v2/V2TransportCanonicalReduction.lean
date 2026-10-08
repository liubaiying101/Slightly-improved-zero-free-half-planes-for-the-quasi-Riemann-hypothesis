import RHZeroFreeExtension.analytic_high.V2TransportGeometry
import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
import RHZeroFreeExtension.analytic_high.V2TransportCanonicalTails
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O

theorem v2_canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (RHV2.boundary:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(RHV2.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-RHV2.smallSaving+8*e)+Z^(-saving)) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  obtain ⟨Cs,hCs,hs⟩ := v2_canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := v2_canonical_large_original_tail K δ a b B ζ saving hδ (by linarith) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=>outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=>Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z
    (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=>Z^(length i)) W0 W1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
      (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=>by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-RHV2.smallSaving+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring


end

end RHZeroFreeExtension.AnalyticHigh
