import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact real geometry of the conditional zero-free extension.
This file proves arithmetic facts only. It imports no analytic RH hypothesis. -/
noncomputable section
namespace RHLowGeometry

def b : ℝ := 1 / 8
def perturbation : ℝ := 1 / 10000
def ell : ℝ := 5003 / 30000
def lx : ℝ := 21247 / 60000
def ly : ℝ := 28747 / 60000
def h : ℝ := 16253 / 20000
def beta0 : ℝ := 34999 / 40000
def lowExponent : ℝ := 7499 / 40000
def signal (s : ℝ) : ℝ := lx / 2 + s - 1 + h / 6

theorem perturbed_ell : ell = 1 / 6 + perturbation := by
  norm_num [ell, perturbation]

theorem scales : lx = (1 - b - ell) / 2 ∧ ly = (1 + b - ell) / 2 ∧
    h = 1 - lx + ell := by norm_num [lx, ly, h, b, ell]

theorem signal_affine (s : ℝ) : signal s = s - 11 / 16 := by
  unfold signal lx h
  ring

theorem low_exact : lx / 2 + b / 12 = lowExponent := by
  norm_num [lx, b, lowExponent]

theorem signal_at_boundary : signal beta0 = lowExponent := by
  norm_num [signal, lx, h, beta0, lowExponent]

theorem boundary_relation : beta0 = 11 / 12 - ell / 4 := by
  norm_num [beta0, ell]

theorem original_improvement : beta0 = 7 / 8 - 1 / 40000 := by
  norm_num [beta0]

theorem length_slacks :
    0 < lx - ell ∧ 0 < ly - ell ∧ 0 < 1 - 3 * ell ∧ ell < 1 / 5 := by
  norm_num [lx, ly, ell]

theorem gram_slack : ly - ell - 11 * b / 6 = 4991 / 60000 := by
  norm_num [ly, ell, b]

theorem gram_positive : 0 < ly - ell - 11 * b / 6 := by
  norm_num [ly, ell, b]

theorem supply_slacks : 8 / 39 < ell / h ∧ 7 / 37 < ell / h ∧
    0 < 5 * ell - h := by norm_num [ell, h]

theorem rescaled_lengths (d : ℝ) (hd : d ≤ ell) :
    0 < lx - d ∧ 0 < ly - d ∧ 0 < 1 - ell - 2 * d ∧
    0 < ly - d - 11 * b / 6 := by
  have hs := length_slacks
  have hg := gram_positive
  constructor
  · linarith [hs.1]
  constructor
  · linarith [hs.2.1]
  constructor
  · linarith [hs.2.2.1]
  · linarith

/-- The positive-part row-energy loss is absorbed by rescaling. -/
theorem compensated_positive_part (d : ℝ) (hd : 0 ≤ d) :
    -d + max (d + 5 * ell - 1) 0 / 8 ≤ -(7 * d) / 8 := by
  have he : 5 * ell - 1 ≤ 0 := by norm_num [ell]
  have hm : max (d + 5 * ell - 1) 0 ≤ d :=
    max_le (by linarith) hd
  linarith

theorem compensated_nonpositive (d : ℝ) (hd : 0 ≤ d) :
    -d + max (d + 5 * ell - 1) 0 / 8 ≤ 0 := by
  have hh := compensated_positive_part d hd
  linarith

/-- Exact identity governing the perturbed reflected-row branch. -/
theorem reflected_length_identity (d : ℝ) :
    1 + 3 * (ell - d) - 2 * (1 - ell - 2 * d) = d + 5 * ell - 1 := by
  ring

/-- Branch reduction, uniformly in every real row-deficit parameter. -/
theorem reflected_branch_bound (d deficit theta error energy : ℝ)
    (hdef : 0 ≤ deficit)
    (hbranch : energy ≤ (1 - ell - 2 * d) +
      (d + 5 * ell - 1 - 2 * deficit + theta) / 4 + error) :
    energy ≤ (1 - ell - 2 * d) + max (d + 5 * ell - 1) 0 / 4 +
      theta / 4 + error := by
  have hm := le_max_left (d + 5 * ell - 1) (0 : ℝ)
  linarith

/-- Exact principal and outer reserves, independent of a target. -/
theorem small_row_reserve :
    ly / 2 - h * (17 / 50 - 1 / 6) - 2 / 100 = 78699 / 1000000 := by
  norm_num [ly, h]

theorem endpoint_reserve :
    1 / 5000 - (45 / 32) * perturbation = (19 / 320000 : ℝ) := by
  norm_num [perturbation]

theorem intermediate_reserve :
    49 / 14400 - (177 / 200) * perturbation = (59657 / 18000000 : ℝ) := by
  norm_num [perturbation]

theorem floor_reserve :
    7 / 1200 - (45 / 32) * perturbation = (1093 / 192000 : ℝ) := by
  norm_num [perturbation]

theorem all_reserves_positive :
    (0 : ℝ) < 78699 / 1000000 ∧ 0 < (19 / 320000 : ℝ) ∧
    0 < (59657 / 18000000 : ℝ) ∧ 0 < (1093 / 192000 : ℝ) := by
  norm_num

/-- Uniform perturbation of any endpoint estimate with the declared slope. -/
theorem perturbed_endpoint_from_slope (oldValue newValue : ℝ)
    (hold : oldValue ≤ -(1 / 5000 : ℝ))
    (hchange : newValue ≤ oldValue + (45 / 32) * perturbation) :
    newValue ≤ -(19 / 320000 : ℝ) := by
  have hr := endpoint_reserve
  linarith

/-- Intermediate/floor bin bounds use only the stated amplitude ranges. -/
theorem intermediate_derivative (delta q : ℝ)
    (hd : delta ≤ 5 / 6) (hq : q ≤ delta / 2) :
    13 / 50 + delta / 4 + q ≤ (177 / 200 : ℝ) := by linarith

theorem intermediate_old_endpoint (delta : ℝ) (hd : delta ≤ 5 / 6) :
    -(529 / 2400 : ℝ) + 25 * delta / 96 ≤ -(49 / 14400 : ℝ) := by
  linarith

theorem moderate_slope (R delta : ℝ)
    (hR : 1 - delta ≤ R) (hd : delta ≤ 5 / 6) :
    (4 / 25 : ℝ) ≤ R + delta / 2 - 17 / 50 := by linarith

theorem intermediate_slope (delta : ℝ) (hd : delta ≤ 5 / 6) :
    0 < (101 / 150 : ℝ) - delta / 6 := by linarith

/-- Existence of a positive fixed extension beyond h with both reserves. -/
theorem extension_exists : ∃ zeta : ℝ, 0 < zeta ∧
    zeta < 5 * ell - h ∧ zeta < (19 / 320000 : ℝ) / 64 := by
  refine ⟨1 / 100000000, ?_⟩
  norm_num [ell, h]


/-- All five good-prime defect powers in the enlarged second region. -/
theorem enlarged_good_exponents (s w z : ℝ) (hs : beta0 ≤ s)
    (hw : 19 / 20 ≤ w) (hz : 33 / 200 ≤ z) :
    -s - w ≤ -(72599 / 40000 : ℝ) ∧
    -s - 6 * z ≤ -(72599 / 40000 : ℝ) ∧
    -w - 6 * z ≤ -(72599 / 40000 : ℝ) ∧
    4 - 6 * s - 6 * z ≤ -(72599 / 40000 : ℝ) ∧
    1 - s - w - 6 * z ≤ -(72599 / 40000 : ℝ) := by
  change (34999 / 40000 : ℝ) ≤ s at hs
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Row-prime boundary powers and the geometric denominator power. -/
theorem enlarged_row_exponents (s w z : ℝ) (hs : beta0 ≤ s)
    (hw : 19 / 20 ≤ w) (hz : 33 / 200 ≤ z) :
    1 - s - w ≤ -(32999 / 40000 : ℝ) ∧
    3 / 2 - 3 * s ≤ -(32999 / 40000 : ℝ) ∧
    2 - 3 * s - w ≤ -(32999 / 40000 : ℝ) ∧
    2 - 4 * s ≤ -(32999 / 40000 : ℝ) ∧
    5 / 2 - 4 * s - w ≤ -(32999 / 40000 : ℝ) ∧
    3 - 6 * s ≤ -(32999 / 40000 : ℝ) ∧
    4 - 6 * s - 6 * z ≤ -(44797 / 20000 : ℝ) := by
  change (34999 / 40000 : ℝ) ≤ s at hs
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Principal selected-prime error powers in the full residue rectangle. -/
theorem principal_error_exponents (s w z : ℝ) (hs : beta0 ≤ s)
    (hw : 19 / 20 ≤ w) (hz : 33 / 200 ≤ z) :
    -s ≤ -beta0 ∧ -6 * z ≤ -beta0 ∧
    4 - 5 * s - 6 * z ≤ -beta0 ∧ 1 - w - 6 * z ≤ -beta0 := by
  change (34999 / 40000 : ℝ) ≤ s at hs
  unfold beta0
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith


/-- The original family bound admits the fixed centered-moment parameter. -/
theorem fixed_kappa_admission (beta : ℝ) (hb : beta ≤ 7 / 8) :
    beta ≤ (1 + (3 / 4 : ℝ)) / 2 := by linarith

/-- All retained non-floor detector bins have the declared delta ceiling. -/
theorem detector_delta_ceiling (beta a : ℝ) (hb : beta ≤ 7 / 8)
    (ha : a ≤ beta) : 2 * a - 1 ≤ (3 / 4 : ℝ) := by linarith

/-- The actual delta range is contained in the enlarged certificate rectangle. -/
theorem detector_certificate_ceiling (beta a : ℝ) (hb : beta ≤ 7 / 8)
    (ha : a ≤ beta) : 2 * a - 1 ≤ (5 / 6 : ℝ) := by linarith

end RHLowGeometry
