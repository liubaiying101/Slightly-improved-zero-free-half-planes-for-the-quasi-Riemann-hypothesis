import OAI.NumberTheory.DirichletL.Hecke.Dirichlet

/-! Generic transfer for the actual Hecke and Dirichlet L-functions.
The Hecke nonvanishing premise is explicit; this file does not prove it.
-/

namespace RHZeroFreeExtension.ActualDirichletTransfer

noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeDirichlet

theorem dirichlet_nonzero_of_hecke_bound
    (boundary : ℝ) (hboundary : 0 < boundary)
    (hHecke : ∀ (eta : Character) (s : ℂ), boundary < s.re →
      (s ≠ 1 ∨ eta.residue ≠ 1) → LFunction eta s ≠ 0)
    (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : boundary < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    chi.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact chi.LFunction_ne_zero_of_one_le_re (not_and_or.mp hpole) hge
  have hsOne : s ≠ 1 := by intro h; simp [h] at hge
  have hsZero : s ≠ 0 := by
    intro h
    norm_num [h] at hs
    linarith
  have h := hHecke (character chi) s hs (Or.inl hsOne)
  rw [LFunction_eq_dirichlet_product chi hsZero hsOne] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_nonzero_of_hecke_bound
    (boundary : ℝ) (hboundary : 0 < boundary)
    (hHecke : ∀ (eta : Character) (s : ℂ), boundary < s.re →
      (s ≠ 1 ∨ eta.residue ≠ 1) → LFunction eta s ≠ 0)
    (s : ℂ) (hs : boundary < s.re) : riemannZeta s ≠ 0 := by
  by_cases hsOne : s = 1
  · simpa [hsOne] using riemannZeta_one_ne_zero
  have h := dirichlet_nonzero_of_hecke_bound boundary hboundary hHecke 1
    (1 : DirichletCharacter ℂ 1) s hs (by simp [hsOne])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end
end RHZeroFreeExtension.ActualDirichletTransfer
