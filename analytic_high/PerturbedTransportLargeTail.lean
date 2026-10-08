import RHZeroFreeExtension.analytic_high.PerturbedTransportLargeDyad
import OAI.NumberTheory.DirichletL.PrimeRows.LargeTail
import RHZeroFreeExtension.analytic_high.PerturbedTransportGeometricTail
set_option linter.unusedVariables false

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma perturbed_absolutePhysicalDyadIntegral_nonneg {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) :
    0≤absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (norm_nonneg _) (physicalDyadNorm_nonneg S hS hmax η R T hT W Yp _ _ _)

theorem perturbed_large_physical_dyads_summable (K : ℕ) (δ a b B r ζ : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r) (hr' : 8/5+δ<r) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(5003/30000:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((66247/40000:ℝ)+((16253/20000:ℝ)+ζ)*(8/5+δ)-ζ*r) := by
  obtain ⟨C,hC,hmain⟩ := perturbed_large_physical_dyad_bound K δ a b B r hδ hδ' hr ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2:ℝ)^(8/5+δ-r)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨C*(1-(2:ℝ)^(8/5+δ-r))⁻¹,mul_pos hC (inv_pos.mpr (sub_pos.mpr hq)),?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z 2 2 r
  let g : ℕ→ℝ := fun n=>Z^((66247/40000:ℝ)+(16253/20000:ℝ)*r)*(Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ
  have hf0 (n : ℕ) : 0≤f n := perturbed_absolutePhysicalDyadIntegral_nonneg S hS hmax η (R n) T hT W _ W0 W1 _ _ _ _ _ _
  have hbnd (n : ℕ) : f n≤A*g n := by
    have hUn : 1≤Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith)) (one_le_pow₀ (by norm_num))
    have hh := hmain η Z (Z^((16253/20000:ℝ)+ζ)*(2:ℝ)^n) hZ hUn (R n) (hR n) T hT hdis length hl0 hl W hWS hWB
    simpa only [A,g,mul_assoc] using hh
  have hg : Summable g := perturbed_large_geometric_summable Z ζ δ r hZ0 hr'
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbnd (hg.mul_left A)
  refine ⟨hf,?_⟩
  calc
    (∑'n,f n) ≤ ∑'n,A*g n := hf.tsum_le_tsum hbnd (hg.mul_left A)
    _ = A*(∑'n,g n) := tsum_mul_left
    _ = A*(Z^((66247/40000:ℝ)+((16253/20000:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
      rw [show (∑'n,g n)=_ from perturbed_large_geometric_sum Z ζ δ r hZ0 hr']
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
