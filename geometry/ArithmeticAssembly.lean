import geometry.Endpoint
import geometry.CountOptimization
import geometry.LowGeometry
import geometry.SlotLengths

/-! Arithmetic closure only. This theorem does not assert nonvanishing of an
L-function and does not construct the physical estimates used by continuation. -/
open scoped BigOperators
namespace RHZeroFreeExtension.Arithmetic
noncomputable section

theorem count_matches_endpoint (δ x : ℝ) :
    RHCount.long δ (RHCount.t δ x) = RHGeometry.R δ x := by
  simp only [RHCount.long, RHCount.t, RHCount.P, RHCount.A, RHCount.J, RHCount.D,
    RHGeometry.R, RHGeometry.P, RHGeometry.J, RHGeometry.D]
  ring

theorem universal_new_endpoint (δ x : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    RHGeometry.E (5003/30000) δ x ≤ -19/320000 ∧
    RHCount.short δ x (RHCount.t δ x) = RHGeometry.R δ x ∧
    1 ≤ RHCount.t δ x ∧ RHCount.t δ x ≤ 3/2 := by
  refine ⟨RHGeometry.perturbed_endpoint δ x hδ0 hδ1 hx0 hx1, ?_,
    (RHCount.t_range δ x hδ0 hδ1 hx0 hx1).1,
    (RHCount.t_range δ x hδ0 hδ1 hx0 hx1).2⟩
  exact (RHCount.balanced_counts δ x hδ0 hδ1 hx0 hx1).trans
    (count_matches_endpoint δ x)

theorem arbitrarily_small_distinct_perturbed_slots (cap : ℝ) (hcap : 0 < cap) :
    ∃ N : ℕ, 0 < N ∧ ∃ ell : Fin N → ℝ, Function.Injective ell ∧
      (∀ j, 0 < ell j ∧ ell j < cap) ∧ (∑ j, ell j) = (5003/30000 : ℝ) := by
  exact RHSlotLengths.exists_distinct_slot_lengths _ cap (by norm_num) hcap

#print axioms universal_new_endpoint
#print axioms arbitrarily_small_distinct_perturbed_slots
end
end RHZeroFreeExtension.Arithmetic
