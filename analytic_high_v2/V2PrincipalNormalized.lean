import geometry.V2AnalyticGeometry
import RHZeroFreeExtension.analytic_high.V2PrincipalPhysicalRemainder
import RHZeroFreeExtension.analytic_high.V2PrincipalResidueActual
import RHZeroFreeExtension.analytic_high.V2RayPoolThresholds
import OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma v2_normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤ c) (hA : ‖A-R‖≤ c) (hN : ‖N⁻¹‖≤ v)
    (hR : ‖R/N-F‖≤ d) : ‖A/N-F‖≤ c*v+d := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem v2_actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hmin : 0< ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=RHV2.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0< e) (hehi : e≤1/1000) (hnu : 0< nu)
    (ha : RHV2.boundary< HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (RHV2.ell)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-((4+RHV2.b)/6)) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-1/3000+nu)+
        Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)+e-(RHV2.boundary)*ellMin)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := v2_physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := v2_normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(RHV2.boundary:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [v2_power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) ell (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0< Z := by linarith
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (RHV2.ell)
    (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(ell j)) (c*Z^ellMin) (Z^(RHV2.y:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := v2_normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(RHV2.boundary:ℝ))=c^(-(RHV2.boundary:ℝ))*Z^(-(RHV2.boundary:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-1/3000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-1/3000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-((4+RHV2.b)/6))*(c*Z^ellMin)^(-(RHV2.boundary:ℝ))=
      (D*c^(-(RHV2.boundary:ℝ)))*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)+e-(RHV2.boundary)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-((4+RHV2.b)/6)+e-(RHV2.boundary)*ellMin=
      (HeckeZeroSupremum.beta+e-((4+RHV2.b)/6))+(-(RHV2.boundary:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤ C := by
    dsimp [C]
    have : 0≤ D*c^(-(RHV2.boundary:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(RHV2.boundary:ℝ))≤ C := by
    dsimp [C]
    have : 0≤ C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)-1/3000+nu)+
        C*Z^(HeckeZeroSupremum.beta-((4+RHV2.b)/6)+e-(RHV2.boundary)*ellMin) := by gcongr
    _ = _ := by ring
end

end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_actual_ray_principal_comparison
