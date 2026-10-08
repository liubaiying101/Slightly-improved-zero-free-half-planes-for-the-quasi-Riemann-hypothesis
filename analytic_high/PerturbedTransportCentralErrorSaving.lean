import OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
set_option linter.unusedVariables false

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma perturbed_central_prime_tuple_count {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(5003/30000:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(5003/30000:ℝ) := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]


lemma perturbed_central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^(21247/60000:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(28747/60000:ℝ))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma perturbed_central_prime_product_bound {K : ℕ} (P : Fin K→PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(5003/30000:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(5003/30000:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma perturbed_central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((16253/20000:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(5003/30000:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(65003/10000:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (16253/20000:ℝ)+ζ≤1 by linarith))
  have hp := perturbed_central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(5003/30000:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((5003/30000:ℝ)*(3:ℕ))=Z^(65003/10000:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


end SevenEighths.ProbeHighRowFamily
end
end OAI
