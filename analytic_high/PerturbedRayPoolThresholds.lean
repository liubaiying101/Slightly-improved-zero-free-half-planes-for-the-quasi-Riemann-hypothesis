import OAI.NumberTheory.DirichletL.Detector.RayPoolGood
import OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
open OAI OAI.SevenEighths
open ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

theorem perturbed_power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0< c) (hd : c≤ d) (hmin : 0< ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin≤ ell j) :
    ∀ᶠZ : ℝ in atTop,
      1≤ Z ∧ 480≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(34999/40000:ℝ))≤1 ∧
      (∀j,480≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)< c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin≤(P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(34999/40000:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<34999/40000)).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0< Z := by linarith
  have hmono (j : ι) : c*Z^ellMin≤ c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

end
end RHZeroFreeExtension.AnalyticHigh
