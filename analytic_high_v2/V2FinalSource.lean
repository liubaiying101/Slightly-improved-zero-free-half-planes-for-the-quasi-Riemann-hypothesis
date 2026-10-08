import analytic_low.V2Normalized
import RHZeroFreeExtension.analytic_high.PerturbedFinalSource
import RHZeroFreeExtension.V2SourceAnalytic
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
def v2_normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (RHV2.ell) (slotMass T (residueWeights W Yp)) : ℂ))

theorem v2_normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=RHV2.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,v2_normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=>Z^(RHV2.lowExponent+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := v2_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=>h.2)⟩

end
end RHZeroFreeExtension.AnalyticHigh
