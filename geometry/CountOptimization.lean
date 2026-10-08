import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
set_option maxHeartbeats 0
namespace RHCount
noncomputable section

def A (x : ℝ) : ℝ := 2-8*x/9
def D (x : ℝ) : ℝ := 3-17*x/9
def P (x : ℝ) : ℝ := A x*(1-x)
def J (δ x : ℝ) : ℝ := (5/6-δ)*D x+δ*P x
def t (δ x : ℝ) : ℝ := 1+δ*P x/(2*J δ x)
def long (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)
def short (δ x t : ℝ) : ℝ := 1-δ+δ*P x/D x*(3/2-t)
def rstar (x t : ℝ) : ℝ := (A x*t-5*x/9)/D x
def inverse (δ x r : ℝ) : ℝ := 1-δ*(x+(1-x)*r)
def plain (δ x t r : ℝ) : ℝ := 1-δ*(4*x/9+A x*(t-r))
def inverseCapacity (r : ℝ) : ℝ := (1-r)/2
def plainCapacity (m : ℝ) : ℝ := 2*(1-2*m)/9

lemma A_lower (x : ℝ) (hx : x ≤ 1/2) : 14/9 ≤ A x := by
  unfold A
  linarith
lemma D_lower (x : ℝ) (hx : x ≤ 1/2) : 37/18 ≤ D x := by
  unfold D
  linarith
lemma P_lower (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 7/9 ≤ P x := by
  unfold P A
  nlinarith [mul_nonneg _hx0 _hx0]
lemma difference_identity (x : ℝ) : D x-P x = 1+x-8*x^2/9 := by
  unfold D P A
  ring
lemma D_ge_P (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : P x ≤ D x := by
  rw [← sub_nonneg]
  rw [difference_identity]
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
lemma J_lower (δ x : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 35/54 ≤ J δ x := by
  have hp := P_lower x hx0 hx1
  have hd := D_ge_P x hx0 hx1
  have hm := mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr hd)
  unfold J at *
  nlinarith

theorem t_range (δ x : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 1 ≤ t δ x ∧ t δ x ≤ 3/2 := by
  have hp := P_lower x hx0 hx1
  have hd := D_lower x hx1
  have hjl := J_lower δ x hδ0 hδ1 hx0 hx1
  have hj : 0 < J δ x := by linarith
  have hn : 0 ≤ δ*P x := mul_nonneg hδ0 (by linarith)
  have hden : δ*P x ≤ J δ x := by
    have hm := mul_nonneg (sub_nonneg.mpr hδ1) (by linarith : 0 ≤ D x)
    unfold J
    linarith
  have hratio0 : 0 ≤ δ*P x/(2*J δ x) := div_nonneg hn (by positivity)
  have hratio1 : δ*P x/(2*J δ x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*J δ x)).2
    linarith
  unfold t
  constructor <;> linarith

theorem balanced_counts (δ x : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : short δ x (t δ x) = long δ (t δ x) := by
  have hd : D x ≠ 0 := ne_of_gt (by linarith [D_lower x hx1])
  have hj : J δ x ≠ 0 := ne_of_gt (by linarith [J_lower δ x hδ0 hδ1 hx0 hx1])
  unfold short long t
  field_simp [hd, hj]
  unfold J
  ring

theorem weighted_identity (δ x t r : ℝ) (hD : D x ≠ 0) :
    (A x*inverse δ x r+(1-x)*plain δ x t r)/D x = short δ x t := by
  unfold inverse plain short
  field_simp [hD]
  unfold D P A
  ring

theorem crossing_identity (δ x t : ℝ) (hD : D x ≠ 0) :
    inverse δ x (rstar x t) = plain δ x t (rstar x t) := by
  unfold inverse plain rstar
  field_simp [hD]
  unfold D A
  ring

theorem rstar_range (x t : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (ht0 : 1 ≤ t) (ht1 : t ≤ 3/2) : 23/37 ≤ rstar x t ∧ rstar x t ≤ 1 := by
  have ha := A_lower x hx1
  have hd : 0 < D x := by linarith [D_lower x hx1]
  have hm0 := mul_nonneg (by linarith : 0 ≤ A x) (sub_nonneg.mpr ht0)
  have hm1 := mul_nonneg (by linarith : 0 ≤ A x) (sub_nonneg.mpr ht1)
  unfold rstar
  constructor
  · apply (le_div_iff₀ hd).2
    unfold A D at *
    nlinarith
  · apply (div_le_iff₀ hd).2
    unfold A D at *
    nlinarith

theorem complementary_range (x t : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (ht0 : 1 ≤ t) (ht1 : t ≤ 3/2) :
    1/3 ≤ t-rstar x t ∧ t-rstar x t ≤ 1/2 := by
  have hd : 0 < D x := by linarith [D_lower x hx1]
  have hden : D x ≠ 0 := ne_of_gt hd
  have hid : t-rstar x t = ((1-x)*t+5*x/9)/D x := by
    unfold rstar
    field_simp [hden]
    unfold D A
    ring
  have hm0 := mul_nonneg (by linarith : 0 ≤ 1-x) (sub_nonneg.mpr ht0)
  have hm1 := mul_nonneg (by linarith : 0 ≤ 1-x) (sub_nonneg.mpr ht1)
  rw [hid]
  constructor
  · apply (le_div_iff₀ hd).2
    unfold D at *
    nlinarith
  · apply (div_le_iff₀ hd).2
    unfold D at *
    nlinarith

theorem inverse_capacity_bound (r : ℝ) (hr0 : 23/37 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ inverseCapacity r ∧ inverseCapacity r ≤ 7/37 := by
  unfold inverseCapacity
  constructor <;> linarith

theorem plain_capacity_bound (m : ℝ) (hm0 : 1/3 ≤ m) (hm1 : m ≤ 1/2) :
    0 ≤ plainCapacity m ∧ plainCapacity m ≤ 2/27 := by
  unfold plainCapacity
  constructor <;> linarith

theorem strict_inverse_margins (r ν z : ℝ) (hr : 23/37 ≤ r) (hν : 0 < ν)
    (hz : z ≤ inverseCapacity r-ν) :
    2*ν ≤ 1-r-2*z ∧ 9/37 ≤ 3-2*r-8*z := by
  unfold inverseCapacity at hz
  constructor <;> linarith


theorem crossing_value (δ x t : ℝ) (hD : D x ≠ 0) :
    inverse δ x (rstar x t) = short δ x t := by
  unfold inverse rstar short
  field_simp [hD]
  unfold D P A
  ring

/-- An affine optimization statement only; no analytic row count is assumed. -/
theorem affine_choice_bound (δ x t r : ℝ) (hδ : 0 ≤ δ)
    (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    min (inverse δ x r) (plain δ x t r) ≤ short δ x t := by
  have hd : D x ≠ 0 := ne_of_gt (by linarith [D_lower x hx1])
  have hv := crossing_value δ x t hd
  have hc := crossing_identity δ x t hd
  rcases le_total r (rstar x t) with hr | hr
  · have hm := mul_nonneg hδ (mul_nonneg (by linarith [A_lower x hx1] : 0 ≤ A x)
        (sub_nonneg.mpr hr))
    have hs : plain δ x t r ≤ plain δ x t (rstar x t) := by
      unfold plain
      nlinarith
    calc
      min (inverse δ x r) (plain δ x t r) ≤ plain δ x t r := min_le_right _ _
      _ ≤ plain δ x t (rstar x t) := hs
      _ = short δ x t := by rw [← hc, hv]
  · have hm := mul_nonneg hδ (mul_nonneg (by linarith : 0 ≤ 1-x)
        (sub_nonneg.mpr hr))
    have hs : inverse δ x r ≤ inverse δ x (rstar x t) := by
      unfold inverse
      nlinarith
    calc
      min (inverse δ x r) (plain δ x t r) ≤ inverse δ x r := min_le_left _ _
      _ ≤ inverse δ x (rstar x t) := hs
      _ = short δ x t := hv

/-- The chosen t balances a decreasing and an increasing affine bound. -/
theorem balance_is_minimax (δ x t' : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    long δ (t δ x) ≤ max (short δ x t') (long δ t') := by
  have hb := balanced_counts δ x hδ0 hδ1 hx0 hx1
  have hp := P_lower x hx0 hx1
  have hd : 0 < D x := by linarith [D_lower x hx1]
  have hs : 0 ≤ δ*P x/D x := div_nonneg
    (mul_nonneg hδ0 (by linarith)) (le_of_lt hd)
  rcases le_total t' (t δ x) with ht | ht
  · have hm := mul_nonneg hs (sub_nonneg.mpr ht)
    have hh : short δ x (t δ x) ≤ short δ x t' := by
      unfold short
      nlinarith
    calc
      long δ (t δ x) = short δ x (t δ x) := hb.symm
      _ ≤ short δ x t' := hh
      _ ≤ max (short δ x t') (long δ t') := le_max_left _ _
  · have hm := mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr ht)
    have hh : long δ (t δ x) ≤ long δ t' := by
      unfold long
      nlinarith
    exact hh.trans (le_max_right _ _)

#print axioms balanced_counts
#print axioms weighted_identity
#print axioms rstar_range
#print axioms complementary_range
#print axioms strict_inverse_margins
#print axioms affine_choice_bound
#print axioms balance_is_minimax
end
end RHCount
