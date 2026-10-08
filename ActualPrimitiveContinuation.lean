import RHZeroFreeExtension.ActualHeckeContinuation
import OAI.NumberTheory.DirichletL.Hecke.PrimitiveSupremum

/-!
The endpoint-independent primitive-supremum deduction for the actual Hecke
family. The premise lists the physical probe estimates and finite-deletion
identity explicitly. Their construction is a separate obligation; this module
does not claim that those estimates have been proved for the new geometry.
-/

namespace RHZeroFreeExtension.ActualPrimitiveContinuation

noncomputable section
open scoped Classical
open Filter Asymptotics
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeZeroSupremum
open RHZeroFreeExtension.ActualHeckeContinuation

theorem beta_le_of_uniform_physical_probes
    (boundary : ℝ) (hhalf : (1 / 2 : ℝ) ≤ boundary)
    (hboundaryOld : boundary ≤ (7 / 8 : ℝ))
    (hprobes : boundary < beta →
      ∃ omega saving : ℝ, 0 < omega ∧ omega < beta - boundary ∧ 0 < saving ∧
        ∀ eta : Character, FiniteFourier.IsPrimitiveOnIdeals eta.residue →
          ∃ (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ) (c : ℝ),
            (∀ I, idealCoeff chi I =
              if IsCoprime I chi.modulus then idealCoeff eta I else 0) ∧
            AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re} ∧
            (∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ)) ∧
            J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)) ∧
            (fun x => J x - HeckeSignal.signal chi H c x) =O[atTop]
              (fun x : ℝ => x ^ (beta + c - saving))) :
    beta ≤ boundary := by
  by_contra hn
  obtain ⟨omega, saving, homega, homegaGap, hsaving, hprobesAll⟩ :=
    hprobes (lt_of_not_ge hn)
  have hmargin : 0 < probeMargin boundary beta omega saving :=
    lt_min (by linarith) hsaving
  have hmarginGap : probeMargin boundary beta omega saving ≤ beta - boundary - omega :=
    min_le_left _ _
  have hsmall : (1 / 2 : ℝ) ≤ beta - probeMargin boundary beta omega saving := by
    linarith
  obtain ⟨eta, rho, hp, hrhoHalf, _, hpole, hz, hnear⟩ :=
    HeckePrimitiveSupremum.exists_primitive_zero_near_beta hmargin hsmall
  obtain ⟨chi, H, J, c, hmask, hH, hcontract, hJ, herror⟩ := hprobesAll eta hp
  have hpoleChi : rho ≠ 1 ∨ chi.residue ≠ 1 := by
    rcases hpole with hOne | hEta
    · exact Or.inl hOne
    · exact Or.inr (fun hChi =>
        hEta ((HeckeFiniteDeletion.principal_iff_of_mask chi eta hmask).mp hChi))
  have hzChi : LFunction chi rho = 0 := by
    rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole chi eta hmask
      (by linarith) hpoleChi, hz, zero_mul]
  exact (nonzero_of_actual_probe_bounds chi H J boundary beta omega saving c
    (by linarith) hboundaryOld beta_le_one homega homegaGap hsaving
    hH hcontract hJ herror hnear hpoleChi) hzChi

theorem hecke_nonzero_of_uniform_physical_probes
    (boundary : ℝ) (hhalf : (1 / 2 : ℝ) ≤ boundary)
    (hboundaryOld : boundary ≤ (7 / 8 : ℝ))
    (hprobes : boundary < beta →
      ∃ omega saving : ℝ, 0 < omega ∧ omega < beta - boundary ∧ 0 < saving ∧
        ∀ eta : Character, FiniteFourier.IsPrimitiveOnIdeals eta.residue →
          ∃ (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ) (c : ℝ),
            (∀ I, idealCoeff chi I =
              if IsCoprime I chi.modulus then idealCoeff eta I else 0) ∧
            AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re} ∧
            (∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ)) ∧
            J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)) ∧
            (fun x => J x - HeckeSignal.signal chi H c x) =O[atTop]
              (fun x : ℝ => x ^ (beta + c - saving)))
    (chi : Character) {s : ℂ} (hs : boundary < s.re)
    (hpole : s ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi s ≠ 0 := by
  exact LFunction_ne_zero_of_beta_lt chi
    ((beta_le_of_uniform_physical_probes boundary hhalf hboundaryOld hprobes).trans_lt hs)
    hpole

end
end RHZeroFreeExtension.ActualPrimitiveContinuation
