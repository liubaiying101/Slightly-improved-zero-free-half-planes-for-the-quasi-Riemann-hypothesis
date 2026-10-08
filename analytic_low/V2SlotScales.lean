import geometry.V2AnalyticGeometry
import OAI.NumberTheory.DirichletL.Detector.LowSlotScales
import analytic_low.V2SourceScales

namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma v2_lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤RHV2.ell)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(RHV2.ell:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤RHV2.ell :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(RHV2.ell:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem v2_eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤RHV2.ell) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^(RHV2.y:ℝ)/L ∧
      1≤(Z^(RHV2.y:ℝ)/L)^2/lowPhysicalScale C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  filter_upwards [v2_eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (v2_lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.ProbePhysical
end

end OAI
