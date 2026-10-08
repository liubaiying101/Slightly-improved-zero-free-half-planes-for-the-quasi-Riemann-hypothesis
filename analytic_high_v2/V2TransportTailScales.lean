import RHZeroFreeExtension.analytic_high.V2TransportGeometry
import OAI.NumberTheory.DirichletL.PrimeRows.TailScales
set_option linter.unusedVariables false
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped BigOperators
open OAI OAI.SevenEighths
open ProbeHighRowFamily
lemma v2_small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(RHV2.ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(RHV2.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+RHV2.canonicalOffset+(17/50:ℝ)-1)*
        (Z^(RHV2.y:ℝ))^((1/2:ℝ)-1))=Z^(β-((4+RHV2.b)/6)-RHV2.sourceSaving+8*e) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  dsimp only [RHV2.sourceSaving, RHV2.smallSaving, RHV2.canonicalOffset, RHV2.largeConstant]
  v2_ring

lemma v2_small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤Z) (hU : 1≤U)
    (hUsmall : U≤Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(RHV2.ell:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(RHV2.x:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+RHV2.canonicalOffset+(17/50:ℝ)-1)*
        (Z^(RHV2.y:ℝ))^((1/2:ℝ)-1))≤Z^(β-((4+RHV2.b)/6)-RHV2.smallSaving+8*e) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,v2_small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-((4+RHV2.b)/6)-RHV2.sourceSaving+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1; dsimp only [RHV2.smallSaving]; ring

lemma v2_large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(RHV2.ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(RHV2.x:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(RHV2.y:ℝ))^((2:ℝ)-1))=
      Z^((RHV2.largeConstant:ℝ)+(RHV2.h:ℝ)*b) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  dsimp only [RHV2.sourceSaving, RHV2.smallSaving, RHV2.canonicalOffset, RHV2.largeConstant]
  v2_ring

end

end RHZeroFreeExtension.AnalyticHigh
