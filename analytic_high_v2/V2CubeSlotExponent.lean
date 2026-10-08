import geometry.V2AnalyticGeometry
import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ProbeHighRowFamily HeckeDetectorPhysicalSelection

lemma v2_source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=RHV2.ell) :
    (∑j∈slots,ell j/d)=RHV2.ell/d := by
  rw [←Finset.sum_div,hell]

lemma v2_source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=RHV2.ell) :
    weightedMean slots (fun j=>ell j/d) g=((RHV2.ell)⁻¹)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  have hL : RHV2.ell≠0 := RHV2.analytic_geometry.1.ne'
  field_simp

lemma v2_source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0< Z) (hd : d≠0) (hell : ∑j∈slots,ell j=RHV2.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-((RHV2.ell*(4/25)):ℝ)+(RHV2.ell)*weightedMean slots (fun j=>ell j/d) g+
        (RHV2.ell)*mesh) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [v2_source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  have hL : RHV2.ell≠0 := RHV2.analytic_geometry.1.ne'
  field_simp

end
end RHZeroFreeExtension.AnalyticHigh
