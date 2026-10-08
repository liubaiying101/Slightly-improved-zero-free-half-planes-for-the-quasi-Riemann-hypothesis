import RHZeroFreeExtension
import RHZeroFreeExtension.V2FullVerification
import geometry.V2Optimization
import geometry.LowGeometry

/-! Correspondence entry for combine_v1.tex.  The definitions below use the
paper's r/new notation.  The zero-free statements are about the actual
upstream Hecke and Dirichlet L-functions, with principal poles excluded.
The analytic constructions are supplied by the full entries, not assumed.
This file does not claim that Lean parses or verifies the TeX prose. -/

namespace CombinedPaper
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

def B_r : ℝ := 34999 / 40000
def b_r : ℝ := 1 / 8
def ell_r : ℝ := 1 / 6 + 1 / 10000
def B_new : ℝ := (1507 - 2 * Real.sqrt 921) / 1653
def b_new : ℝ := -4 / 29 + 230 * Real.sqrt 921 / 26709
def ell_new : ℝ := (33 + 8 * Real.sqrt 921) / 1653

theorem rational_parameters : b_r = RHLowGeometry.b ∧
    ell_r = RHLowGeometry.ell ∧ B_r = RHLowGeometry.beta0 := by
  norm_num [b_r, ell_r, B_r, RHLowGeometry.b, RHLowGeometry.ell,
    RHLowGeometry.beta0]

theorem algebraic_parameters : b_new = RHV2.b ∧
    ell_new = RHV2.ell ∧ B_new = RHV2.boundary := by
  exact ⟨rfl, rfl, rfl⟩

theorem balanced_signal_matching (b ell : ℝ) :
    (11 / 12 - ell / 4) - (4 + b) / 6 =
      ((1 - b - ell) / 2) / 2 + b / 12 := by
  ring

theorem rational_boundary : B_r = 11 / 12 - ell_r / 4 ∧
    (7 / 8 : ℝ) - B_r = 1 / 40000 := by
  norm_num [B_r, ell_r]

theorem algebraic_boundary : B_new = 11 / 12 - ell_new / 4 := by
  exact RHV2.boundary_identity

theorem boundary_order : B_new < B_r ∧ B_r < (7 / 8 : ℝ) := by
  constructor
  · exact RHV2.gate_v1_improvement
  · norm_num [B_r]

/-- Part I's original supremum conclusion. -/
theorem original_family_bound : HeckeZeroSupremum.beta ≤ (7 / 8 : ℝ) :=
  RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths

/-- The weaker 11/12 conclusion, asserted in Part I.  This is a deduction
from the original verified 7/8 conclusion, not a formalization of the
historical preliminary proof in Part I. -/
theorem preliminary_family_bound : HeckeZeroSupremum.beta ≤ (11 / 12 : ℝ) :=
  original_family_bound.trans (by norm_num)

/-- Part II, Theorem 15.1. -/
theorem rational_family_bound : HeckeZeroSupremum.beta ≤ B_r :=
  RHZeroFreeExtension.beta_star_le

theorem rational_hecke_nonzero (eta : Character) (s : ℂ)
    (hs : B_r < s.re) (hpole : s ≠ 1 ∨ eta.residue ≠ 1) :
    LFunction eta s ≠ 0 :=
  RHZeroFreeExtension.hecke_nonzero eta s hs hpole

theorem rational_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : B_r < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  RHZeroFreeExtension.dirichlet_nonzero q hq chi s hs hpole

theorem rational_zeta_nonzero (s : ℂ) (hs : B_r < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 :=
  RHZeroFreeExtension.zeta_nonzero s hs hpole

/-- Part III, Theorem 21.1, and the introductory main theorem. -/
theorem algebraic_family_bound : HeckeZeroSupremum.beta ≤ B_new :=
  RHV2.beta_star_le

theorem algebraic_hecke_nonzero (eta : Character) (s : ℂ)
    (hs : B_new < s.re) (hpole : s ≠ 1 ∨ eta.residue ≠ 1) :
    LFunction eta s ≠ 0 :=
  RHV2.hecke_nonzero eta s hs hpole

theorem algebraic_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : B_new < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  RHV2.dirichlet_nonzero q hq chi s hs hpole

theorem algebraic_zeta_nonzero (s : ℂ) (hs : B_new < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 :=
  RHV2.zeta_nonzero s hs hpole

/-- Part I's Hecke conclusion, with the pole condition made explicit. -/
theorem original_hecke_nonzero (eta : Character) (s : ℂ)
    (hs : (7 / 8 : ℝ) < s.re) (hpole : s ≠ 1 ∨ eta.residue ≠ 1) :
    LFunction eta s ≠ 0 := by
  apply rational_hecke_nonzero eta s (lt_trans boundary_order.2 hs) hpole

theorem original_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  rational_dirichlet_nonzero q hq chi s (lt_trans boundary_order.2 hs) hpole

theorem original_zeta_nonzero (s : ℂ) (hs : (7 / 8 : ℝ) < s.re)
    (hpole : s ≠ 1) : riemannZeta s ≠ 0 :=
  rational_zeta_nonzero s (lt_trans boundary_order.2 hs) hpole

/-- Part II's uniform rational endpoint lemma. -/
theorem rational_endpoint (delta x : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    RHGeometry.E (5003 / 30000) delta x ≤ -(19 / 320000 : ℝ) := by
  simpa only [neg_div] using RHGeometry.perturbed_endpoint delta x hd0 hd1 hx0 hx1

/-- Part III's endpoint inequality. -/
theorem algebraic_endpoint (delta x : ℝ)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 5 / 6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : RHV2.E delta x ≤ 0 :=
  RHV2.universal_endpoint delta x hd0 hd1 hx0 hx1

/-- The dual obstruction, retaining exactly its three numerical premises. -/
theorem scalar_obstruction (M ell B : ℝ)
    (h0 : 5 / 6 + M / 12 - ell / 6 ≤ B)
    (hK : 1 / 3 + 7 * M / 12 + ell / 3 ≤ B)
    (hH : 1 + RHV2.dc - (1 + RHV2.dc) * M / 2 + RHV2.dc * ell ≤ B) :
    B_new ≤ B := RHV2.closure_obstruction M ell B h0 hK hH

#print axioms rational_parameters
#print axioms algebraic_parameters
#print axioms balanced_signal_matching
#print axioms rational_boundary
#print axioms algebraic_boundary
#print axioms boundary_order
#print axioms original_family_bound
#print axioms preliminary_family_bound
#print axioms rational_family_bound
#print axioms rational_hecke_nonzero
#print axioms rational_dirichlet_nonzero
#print axioms rational_zeta_nonzero
#print axioms algebraic_family_bound
#print axioms algebraic_hecke_nonzero
#print axioms algebraic_dirichlet_nonzero
#print axioms algebraic_zeta_nonzero
#print axioms original_hecke_nonzero
#print axioms original_dirichlet_nonzero
#print axioms original_zeta_nonzero
#print axioms rational_endpoint
#print axioms algebraic_endpoint
#print axioms scalar_obstruction

end
end CombinedPaper
