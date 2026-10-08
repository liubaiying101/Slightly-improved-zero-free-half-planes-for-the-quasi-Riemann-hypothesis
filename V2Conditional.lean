import geometry.V2Optimization
import RHZeroFreeExtension.ActualPrimitiveContinuation
import RHZeroFreeExtension.ActualDirichletTransfer

/-! Actual analytic statements at the v2 boundary, CONDITIONAL on constructing
physical probes at the new radical geometry. The premise is explicit and is
not an axiom. V2Optimization proves the scalar certificates, not this premise.
-/
namespace RHV2
noncomputable section
open scoped Classical
open Filter Asymptotics
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeZeroSupremum

/-- The exact missing analytic obligation, preserving the actual coefficient
mask, primitive family, holomorphic correction and asymptotic quantifiers. -/
def PhysicalProbeEstimates : Prop := boundary < beta →
  ∃ omega saving : ℝ, 0 < omega ∧ omega < beta - boundary ∧ 0 < saving ∧
    ∀ eta : Character, FiniteFourier.IsPrimitiveOnIdeals eta.residue →
      ∃ (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ) (c : ℝ),
        (∀ I, idealCoeff chi I =
          if IsCoprime I chi.modulus then idealCoeff eta I else 0) ∧
        AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re} ∧
        (∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1/2 : ℝ)) ∧
        J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)) ∧
        (fun x => J x - HeckeSignal.signal chi H c x) =O[atTop]
          (fun x : ℝ => x ^ (beta + c - saving))

/-- CONDITIONAL v2 supremum bound. The proof does not construct hprobes. -/
theorem beta_star_le_of_probes (hprobes : PhysicalProbeEstimates) : beta ≤ boundary := by
  apply RHZeroFreeExtension.ActualPrimitiveContinuation.beta_le_of_uniform_physical_probes
    boundary (by linarith [gate_boundary_domain])
    (by linarith [gate_v1_improvement]) hprobes

theorem hecke_nonzero_of_probes (hprobes : PhysicalProbeEstimates)
    (chi : Character) (z : ℂ) (hz : boundary < z.re)
    (hpole : z ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi z ≠ 0 :=
  LFunction_ne_zero_of_beta_lt chi ((beta_star_le_of_probes hprobes).trans_lt hz) hpole

theorem dirichlet_nonzero_of_probes (hprobes : PhysicalProbeEstimates)
    (q : ℕ) (hq : q ≠ 0) (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : boundary < z.re) (hpole : ¬ (chi = 1 ∧ z = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi z ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  apply RHZeroFreeExtension.ActualDirichletTransfer.dirichlet_nonzero_of_hecke_bound
    boundary (by linarith [gate_boundary_domain]) ?_ q chi z hz hpole
  intro eta s hs hp
  exact hecke_nonzero_of_probes hprobes eta s hs hp

theorem zeta_nonzero_of_probes (hprobes : PhysicalProbeEstimates)
    (z : ℂ) (hz : boundary < z.re) (_hpole : z ≠ 1) : riemannZeta z ≠ 0 := by
  apply RHZeroFreeExtension.ActualDirichletTransfer.zeta_nonzero_of_hecke_bound
    boundary (by linarith [gate_boundary_domain]) ?_ z hz
  intro eta s hs hp
  exact hecke_nonzero_of_probes hprobes eta s hs hp

#print axioms beta_star_le_of_probes
#print axioms hecke_nonzero_of_probes
#print axioms dirichlet_nonzero_of_probes
#print axioms zeta_nonzero_of_probes
end
end RHV2
