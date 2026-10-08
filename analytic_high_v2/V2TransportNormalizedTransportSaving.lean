import RHZeroFreeExtension.analytic_high.V2TransportGeometry
import RHZeroFreeExtension.analytic_high.V2CubeNormalizer
import RHZeroFreeExtension.analytic_high.V2PrincipalNormalized
import OAI.NumberTheory.DirichletL.PrimeRows.NormalizedTransportSaving
import RHZeroFreeExtension.analytic_high.V2TransportNormalizedTransport
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem v2_transportSavingPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem v2_actual_normalized_probe_transport_saving (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (RHV2.boundary:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=RHV2.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0<sigma)
    (_hgeometric : sigma+8*e+nu≤RHV2.smallSaving) (hprincipal : sigma+nu≤1/3000)
    (hwindow : sigma+e≤(RHV2.boundary)*ellMin) (hlarge : sigma+nu≤saving+RHV2.lowExponent) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := v2_transportSavingPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHV2.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-((4+RHV2.b)/6)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((RHV2.h:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-sigma) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  have hMatching := RHV2.lowExponent_signal
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,hbound⟩ := v2_actual_normalized_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨C,hC,hb⟩ := hbound η
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  dsimp only at hb ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := hb
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,herror.trans ?_⟩
  have h1 : Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-RHV2.smallSaving+8*e+nu)≤Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h2 : Z^(-saving+nu)≤Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h3 : Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-1/3000+nu)≤Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h4 : Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)+e-(RHV2.boundary)*ellMin)≤Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ C*(4*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-sigma)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ = _ := by ring


end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_actual_normalized_probe_transport_saving
