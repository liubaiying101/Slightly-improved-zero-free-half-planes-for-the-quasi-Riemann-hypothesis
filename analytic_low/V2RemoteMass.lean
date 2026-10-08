import geometry.V2AnalyticGeometry
import OAI.NumberTheory.DirichletL.Detector.LowRemoteMass
import analytic_low.PerturbedNominalGeometry
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
lemma v2_canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤RHV2.ell) (b Z : ℝ) (hZ : 1≤Z)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(RHV2.ell:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      apply Finset.prod_le_prod₀ (fun i _=>Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma v2_compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤RHV2.ell)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=>Z^(RHV2.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^(RHV2.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(RHV2.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(RHV2.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^((1-RHV2.ell):ℝ) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    have hcoeff : ‖compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun (i : SelectedSlot J) _=>hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [perturbed_lowPhysicalScale_source (RHV2.ell) (RHV2.x) (RHV2.y) (by v2_geometry) C Z _ hz]
    rw [show (1-(RHV2.ell:ℝ))=(1-RHV2.ell) by v2_geometry]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (v2_canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤elementNorm C.generator*Z^((1-RHV2.ell):ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(RHV2.ell:ℝ)*Z^((1-RHV2.ell):ℝ)) := by v2_ring
    _=_ := by rw [←Real.rpow_add hz];v2_geometry

end SevenEighths.ProbePhysical
end

end OAI
