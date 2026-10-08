import OAI.NumberTheory.DirichletL.Hecke.SignalIdentity

/-!
Generic continuation for the actual upstream Hecke L-function and signal.
This proves an implication from explicit probe estimates. It does not construct
those estimates and does not assert the improved zero-free theorem.
-/

namespace RHZeroFreeExtension.ActualHeckeContinuation

noncomputable section
open Filter Asymptotics Set
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeSignal OAI.SevenEighths.Continuation

def probeMargin (boundary beta omega saving : ℝ) : ℝ :=
  min (beta - boundary - omega) saving

theorem nonzero_of_actual_probe_bounds
    (chi : Character) (H : ℂ → ℂ) (J : ℝ → ℂ)
    (boundary beta omega saving c : ℝ)
    (hboundary : 0 < boundary) (hboundaryOld : boundary ≤ (7 / 8 : ℝ))
    (hbeta : beta ≤ 1) (homega : 0 < omega)
    (homegaGap : omega < beta - boundary) (hsaving : 0 < saving)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re})
    (hcontract : ∀ s : ℂ, boundary < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (boundary + c + omega)))
    (herror : (fun x => J x - signal chi H c x) =O[atTop]
      (fun x : ℝ => x ^ (beta + c - saving)))
    {rho : ℂ}
    (hrho : beta - probeMargin boundary beta omega saving < rho.re)
    (hpole : rho ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi rho ≠ 0 := by
  let a := beta - probeMargin boundary beta omega saving
  have hmargin : 0 < probeMargin boundary beta omega saving := by
    exact lt_min (by linarith) hsaving
  have hmarginGap : probeMargin boundary beta omega saving ≤ beta - boundary - omega :=
    min_le_left _ _
  have hboundaryA : boundary < a := by dsimp [a]; linarith
  have haTwo : a < 2 := by dsimp [a]; linarith
  have hexponents : max (boundary + c + omega) (beta + c - saving) = a + c := by
    dsimp only [a, probeMargin]
    rcases le_total (beta - boundary - omega) saving with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right h, max_eq_right (by linarith)]
      ring
  have htop : signal chi H c =O[atTop] (fun x : ℝ => x ^ (a + c)) := by
    simpa only [hexponents] using
      common_signal_bound J (signal chi H c) (boundary + c + omega)
        (beta + c - saving) hJ herror
  have hHOld : AnalyticOnNhd ℂ H {s : ℂ | (7 / 8 : ℝ) < s.re} :=
    hH.mono (fun _ hs => lt_of_le_of_lt hboundaryOld hs)
  have hcontractOld : ∀ s : ℂ, (7 / 8 : ℝ) < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ) :=
    fun s hs => hcontract s (lt_of_le_of_lt hboundaryOld hs)
  have hHd := hHOld.differentiableOn
  have hHa : AnalyticOnNhd ℂ H {s : ℂ | a < s.re} :=
    hH.mono (fun _ hs => lt_trans hboundaryA hs)
  have hregularAnalytic : AnalyticOnNhd ℂ (regularL chi) {s : ℂ | a < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (regularL_entire chi)).mono
      (Set.subset_univ _)
  have hregularizerAnalytic : AnalyticOnNhd ℂ (targetRegularizer chi)
      {s : ℂ | a < s.re} :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (targetRegularizer_entire chi)).mono (Set.subset_univ _)
  have hidentity : ∀ s : ℂ, max a 1 < s.re →
      regularL chi s * signalMellin (signal chi H c) c s =
        targetRegularizer chi s * gaussianMultiplier H s := by
    intro s hs
    have hsOne : 1 < s.re := (le_max_right a 1).trans_lt hs
    have hsZero : s ≠ 0 := by intro h; norm_num [h] at hsOne
    have hsNotOne : s ≠ 1 := by intro h; norm_num [h] at hsOne
    rw [regularL_eq chi hsZero (Or.inl hsNotOne),
      signalMellin_eq_amplitude chi H hHd hcontractOld c a haTwo htop hs]
    unfold amplitude quotient gaussianMultiplier
    rw [OAI.SevenEighths.HeckeReciprocal.reciprocal_eq_inv chi hsZero hsNotOne]
    have hnonzero := LFunction_ne_zero_of_one_lt_re chi hsOne
    field_simp
  have hrhoA : a < rho.re := hrho
  have hrhoZero : rho ≠ 0 := by
    intro h
    rw [h] at hrhoA
    norm_num at hrhoA
    linarith
  exact nonzero_of_regularized_signal a 1 c (LFunction chi) (regularL chi)
    (targetRegularizer chi) (gaussianMultiplier H) (signal chi H c)
    hregularAnalytic hregularizerAnalytic (gaussianMultiplier_analytic hHa)
    (signal_locallyIntegrable chi H hHd hcontractOld c) htop
    (signal_rapidDecayAtZero chi H hHd hcontractOld c) hidentity hrhoA
    (regularL_eq chi hrhoZero hpole) (targetRegularizer_ne_zero chi hpole)
    (gaussianMultiplier_ne_zero (hcontract rho (hboundaryA.trans hrhoA)))

end
end RHZeroFreeExtension.ActualHeckeContinuation
