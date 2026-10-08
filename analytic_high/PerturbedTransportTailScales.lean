import OAI.NumberTheory.DirichletL.PrimeRows.TailScales
set_option linter.unusedVariables false
namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily
lemma perturbed_small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(5003/30000:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(21247/60000:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+1/40000+(17/50:ℝ)-1)*
        (Z^(28747/60000:ℝ))^((1/2:ℝ)-1))=Z^(β-11/16-49337/500000+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

lemma perturbed_small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤Z) (hU : 1≤U)
    (hUsmall : U≤Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(5003/30000:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(21247/60000:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+1/40000+(17/50:ℝ)-1)*
        (Z^(28747/60000:ℝ))^((1/2:ℝ)-1))≤Z^(β-11/16-39337/500000+8*e) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,perturbed_small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-11/16-49337/500000+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1;ring

lemma perturbed_large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(5003/30000:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(21247/60000:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(28747/60000:ℝ))^((2:ℝ)-1))=
      Z^((66247/40000:ℝ)+(16253/20000:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
