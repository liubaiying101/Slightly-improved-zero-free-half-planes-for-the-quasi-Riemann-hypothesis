import RHZeroFreeExtension.analytic_high.PerturbedFinalUnconditional
import geometry.ArithmeticAssembly

/-! Public entry point for the kernel-checked zero-free extension.
The implementation imports the actual pinned original source theorem and
constructs the new moment input. The public conclusions have no additional
analytic hypothesis; their transitive axioms are propext, Classical.choice
and Quot.sound. Replay with check_extension.sh; exact source hashes and
acceptance logs are recorded under audits/extension_replay/.
-/
namespace RHZeroFreeExtension
noncomputable section
open OAI.SevenEighths HeckeFamily

/-- The supremum used in the manuscript, over the actual finite-residue Hecke family over the Eisenstein field, with
sentinel one half, is at most the exact rational 34999/40000. -/
theorem beta_star_le : HeckeZeroSupremum.beta ≤ (34999/40000 : ℝ) :=
  AnalyticHigh.actual_beta_le_new_boundary

theorem hecke_nonzero (chi : Character) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi s ≠ 0 :=
  AnalyticHigh.actual_hecke_nonzero chi s hs hpole

theorem dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  AnalyticHigh.actual_dirichlet_nonzero q hq chi s hs hpole

/-- Classical zero-free assertion away from the pole at one. -/
theorem zeta_nonzero (s : ℂ) (hs : (34999/40000 : ℝ) < s.re) (_hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := AnalyticHigh.actual_zeta_nonzero s hs

#print axioms beta_star_le
#print axioms hecke_nonzero
#print axioms dirichlet_nonzero
#print axioms zeta_nonzero
end
end RHZeroFreeExtension
