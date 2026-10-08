import geometry.V2AnalyticGeometry
import OAI.NumberTheory.DirichletL.Detector.LowSourceScales
import OAI.NumberTheory.DirichletL.Detector.LowTupleGram
import OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma v2_source_gram_power (Z δ : ℝ) (hZ : 0<Z) :
    Z^(RHV2.x:ℝ)*(Z^(RHV2.b:ℝ))^(1/6:ℝ)*(Z^(RHV2.y:ℝ))^δ=
      Z^(RHV2.gramExponent+(RHV2.y)*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  v2_ring

lemma v2_source_gram_sqrt_power (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^(RHV2.gramExponent+(RHV2.y)*δ:ℝ))=Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  v2_ring

lemma v2_source_scale_ratio (Z : ℝ) (hZ : 0<Z) :
    Z^(RHV2.y:ℝ)/Z^(RHV2.x:ℝ)=Z^(RHV2.b:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [←Real.rpow_sub hZ]
  v2_geometry

lemma v2_source_scale_square (Z : ℝ) (hZ : 0<Z) :
    Z^((2*RHV2.x-RHV2.y):ℝ)*Z^(RHV2.y:ℝ)=(Z^(RHV2.x:ℝ))^2 := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  v2_geometry

lemma v2_source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(RHV2.b:ℝ)) (hLl : L≤Z^((2*RHV2.x-RHV2.y):ℝ)) :
    1≤Z^(RHV2.y:ℝ)/L ∧
    q*Z^(RHV2.x:ℝ)≤Z^(RHV2.y:ℝ) ∧
    L*Z^(RHV2.y:ℝ)≤q^2*(Z^(RHV2.x:ℝ))^2 := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*RHV2.x-RHV2.y):ℝ)≤RHV2.y by v2_geometry))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (RHV2.x))).mp
    rwa [v2_source_scale_ratio Z hz]
  · calc
      _≤Z^((2*RHV2.x-RHV2.y):ℝ)*Z^(RHV2.y:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(RHV2.x:ℝ))^2 := v2_source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma v2_source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(RHV2.b:ℝ)) (hLl : L≤Z^((2*RHV2.x-RHV2.y):ℝ)) (hδ : 0≤δ) :
    (q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)/(Z^(RHV2.y:ℝ)/L))*
      (1+((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^2/(Z^(RHV2.y:ℝ)/L))*
      (Z^(RHV2.y:ℝ)/L)^δ ≤
        (3*q/L)*Z^(RHV2.gramExponent+(RHV2.y)*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := v2_source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(RHV2.y:ℝ)/(q*Z^(RHV2.x:ℝ))≤Z^(RHV2.b:ℝ) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    rw [←v2_source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(RHV2.y:ℝ)/(q*Z^(RHV2.x:ℝ))) hratio (show 0≤(1/6:ℝ) by v2_geometry)
  calc
    _≤3*(q*Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.b:ℝ))^(1/6:ℝ)*(Z^(RHV2.y:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(RHV2.x:ℝ)*(Z^(RHV2.b:ℝ))^(1/6:ℝ)*(Z^(RHV2.y:ℝ))^δ) := by v2_ring
    _=_ := by rw [v2_source_gram_power Z δ hz]

lemma v2_source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(RHV2.b:ℝ)) (hLl : L≤Z^((2*RHV2.x-RHV2.y):ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)/(Z^(RHV2.y:ℝ)/L))*
      (1+((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^2/(Z^(RHV2.y:ℝ)/L))*
      (Z^(RHV2.y:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  apply (Real.sqrt_le_sqrt (v2_source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),v2_source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma v2_lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(RHV2.b:ℝ))
    (hLl : L≤Z^((2*RHV2.x-RHV2.y):ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) :=
  v2_source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma v2_eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(RHV2.b:ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^(RHV2.ell:ℝ)→
        1≤Z^(RHV2.y:ℝ)/L ∧
        1≤(Z^(RHV2.y:ℝ)/L)^2/lowPhysicalScale C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hq := (tendsto_rpow_atTop (show 0<(RHV2.b:ℝ) by v2_geometry)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((3/50):ℝ) by v2_geometry)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^((2*RHV2.x-RHV2.y):ℝ) := calc
    L≤B*Z^(RHV2.ell:ℝ) := hLB
    _≤Z^((3/50):ℝ)*Z^(RHV2.ell:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((3/50+RHV2.ell):ℝ) := by rw [←Real.rpow_add hz]
    _≤Z^((2*RHV2.x-RHV2.y):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by v2_geometry)
  obtain ⟨hy,hp,_⟩ := v2_source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>v2_lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI
