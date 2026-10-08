import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ProbeHighRowFamily HeckeDetectorPhysicalSelection

lemma perturbed_source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=5003/30000) :
    (∑j∈slots,ell j/d)=5003/(30000*d) := by
  rw [←Finset.sum_div,hell]
  ring

lemma perturbed_source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=5003/30000) :
    weightedMean slots (fun j=>ell j/d) g=(30000/5003)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma perturbed_source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0< Z) (hd : d≠0) (hell : ∑j∈slots,ell j=5003/30000) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(5003/187500:ℝ)+(5003/30000)*weightedMean slots (fun j=>ell j/d) g+
        (5003/30000)*mesh) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [perturbed_source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  ring

end
end RHZeroFreeExtension.AnalyticHigh
