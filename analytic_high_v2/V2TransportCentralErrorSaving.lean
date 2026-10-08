import RHZeroFreeExtension.analytic_high.V2TransportGeometry
import OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
import OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma v2_central_prime_tuple_count {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(RHV2.ell:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(RHV2.ell:ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
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


lemma v2_central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^(RHV2.x:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(RHV2.y:ℝ))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by
    have haY := mul_nonneg hYpos.le ha
    have heY := mul_nonneg hYpos.le he
    nlinarith only [hXhi, haY, heY])

lemma v2_central_prime_product_bound {K : ℕ} (P : Fin K→PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(RHV2.ell:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(RHV2.ell:ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma v2_central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((RHV2.h:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(RHV2.ell:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^((6+3*RHV2.ell):ℝ) := by
  obtain ⟨hOff, hSmall, hHhi, hHpos, hEllhi, hXpos, hXhi, hYpos, hYhi, hBclo, hBchi⟩ := RHV2.transport_geometry
  have hCanonical : RHV2.boundary+RHV2.canonicalOffset = 7/8 := by dsimp [RHV2.canonicalOffset]; ring
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (RHV2.h:ℝ)+ζ≤1 by linarith))
  have hp := v2_central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(RHV2.ell:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((RHV2.ell:ℝ)*(3:ℕ))=Z^((6+3*RHV2.ell):ℝ) := by rw [←Real.rpow_add hZ0]; congr 1; ring
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring


end
end RHZeroFreeExtension.AnalyticHigh
