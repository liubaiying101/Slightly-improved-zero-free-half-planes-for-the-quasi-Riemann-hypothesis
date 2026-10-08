import RHZeroFreeExtension.analytic_high.PerturbedPrincipalSlot
import RHZeroFreeExtension.analytic_high.PerturbedFiniteProduct

set_option linter.unusedVariables false

/-! Sharp fixed positive slot bounds for the genuine finite Euler product.
This derives the new exponent in the small-prime error from proved local
unit cancellation; no sharp product estimate is an input.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss HeckeFamily ProbePhysical ProbeEuler ProbeLocal ProbeFiniteProductBounds
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

theorem perturbed_slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 34999/40000≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(34999/40000 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using perturbed_weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem perturbed_combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : 34999/40000≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(34999/40000 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (perturbed_global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (perturbed_slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)


end
end RHZeroFreeExtension.AnalyticHigh
