import geometry.CountOptimization
import Mathlib.Analysis.Real.Sqrt
/-! Exact algebra of derived_zero_free_extension_v2.tex. No analytic claim is
postulated. This file checks the endpoint and the declared scalar closure. -/
set_option maxHeartbeats 0
namespace RHV2
noncomputable section
def s : ℝ := Real.sqrt 921
lemma s_sq : s^2 = 921 := by norm_num [s, Real.sq_sqrt]
lemma s_bounds : (30347/1000 : ℝ) < s ∧ s < (30348/1000 : ℝ) := by
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  constructor <;> nlinarith [s_sq]
def ell : ℝ := (33+8*s)/1653
def b : ℝ := -4/29+230*s/26709
def x : ℝ := (1-b-ell)/2
def y : ℝ := (1+b-ell)/2
def h : ℝ := (1+b+3*ell)/2
def dc : ℝ := (49-s)/48
def boundary : ℝ := (1507-2*s)/1653
def C0 : ℝ := -1/4+b/6+5*ell/4
def R (d u : ℝ) : ℝ := 1-d+(5/6-d)*d*RHCount.P u/(2*RHCount.J d u)
def E (d u : ℝ) : ℝ := C0+(1/2+ell)*d+ell*(u*d)-h*(1-R d u)
def Q (d v : ℝ) : ℝ :=
  -2*(185+170*v+(-138+12*v+96*v^2)*d)*C0+
  (185+170*v+(-138+12*v+96*v^2)*d)*(b+2*ell*v)*d-
  12*h*(5/6-d)*d*(7+18*v+8*v^2)
def Ac (v : ℝ) : ℝ := ((31824/551 : ℝ) - 36688*s/169157) + (214096*s/169157 + (50916/551 : ℝ)) * v^1 + (347296*s/169157 + (17352/551 : ℝ)) * v^2 + (512*s/551 + (2112/551 : ℝ)) * v^3
def Dc (v : ℝ) : ℝ := (1445960*s/507471 + (-69560/551 : ℝ)) + (504040*s/507471 + (-51290/551 : ℝ)) * v^1 + ((9660/551 : ℝ) - 363760*s/507471) * v^2
def Gc (v : ℝ) : ℝ := ((151700/1653 : ℝ) - 4216150*s/1522413) + ((139400/1653 : ℝ) - 3874300*s/1522413) * v^1
def disc (v : ℝ) : ℝ := (0) + ((3861265032800/279616521 : ℝ) - 122715443200*s/279616521) * v^1 + ((2386327618300/279616521 : ℝ) - 19093999200*s/93205507) * v^2 + (46823488000*s/93205507 + (-3389811480400/279616521 : ℝ)) * v^3 + (4408611200*s/14716659 + (-40221718800/4905553 : ℝ)) * v^4
lemma quadratic_identity (d v : ℝ) : Q d v = Ac v*d^2+Dc v*d+Gc v := by
  simp only [Q, C0, b, ell, h, Ac, Dc, Gc]
  ring
lemma discriminant_identity (v : ℝ) : 4*Ac v*Gc v-(Dc v)^2 = disc v := by
  unfold Ac Gc Dc disc
  ring_nf
  simp only [s_sq]
  ring
lemma complete_square (d v : ℝ) :
    4*Ac v*Q d v = (2*Ac v*d+Dc v)^2+disc v := by
  rw [quadratic_identity, ← discriminant_identity]
  ring
lemma Ac_coeff_0_pos : 0 < ((31824/551 : ℝ) - 36688*s/169157 : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_coeff_1_pos : 0 < (214096*s/169157 + (50916/551 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_coeff_2_pos : 0 < (347296*s/169157 + (17352/551 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_coeff_3_pos : 0 < (512*s/551 + (2112/551 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_pos (v : ℝ) (hv : 0 ≤ v) : 0 < Ac v := by
  have hc0 := Ac_coeff_0_pos
  have hc1 := Ac_coeff_1_pos
  have hc2 := Ac_coeff_2_pos
  have hc3 := Ac_coeff_3_pos
  have hv2 : 0 ≤ v^2 := sq_nonneg v
  have hv3 : 0 ≤ v^3 := pow_nonneg hv _
  unfold Ac
  positivity
lemma disc_coeff_1_pos : 0 < ((3861265032800/279616521 : ℝ) - 122715443200*s/279616521 : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_coeff_2_pos : 0 < ((2386327618300/279616521 : ℝ) - 19093999200*s/93205507 : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_coeff_3_pos : 0 < (46823488000*s/93205507 + (-3389811480400/279616521 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_coeff_4_pos : 0 < (4408611200*s/14716659 + (-40221718800/4905553 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_nonneg (v : ℝ) (hv : 0 ≤ v) : 0 ≤ disc v := by
  have hc1 := disc_coeff_1_pos
  have hc2 := disc_coeff_2_pos
  have hc3 := disc_coeff_3_pos
  have hc4 := disc_coeff_4_pos
  have hv2 : 0 ≤ v^2 := sq_nonneg v
  have hv3 : 0 ≤ v^3 := pow_nonneg hv _
  have hv4 : 0 ≤ v^4 := pow_nonneg hv _
  unfold disc
  positivity
theorem Q_nonneg (d v : ℝ) (hv : 0 ≤ v) : 0 ≤ Q d v := by
  have ha := Ac_pos v hv
  have hh := complete_square d v
  have hd := disc_nonneg v hv
  have hs := sq_nonneg (2*Ac v*d+Dc v)
  have hm : 0 ≤ 4*Ac v*Q d v := by linarith
  exact nonneg_of_mul_nonneg_right hm (by positivity)
lemma exponent_identity (d u : ℝ) (hj : RHCount.J d u ≠ 0) :
    Q d (1/2-u) = 216*RHCount.J d u*(-E d u) := by
  unfold Q E R
  field_simp [hj]
  simp only [RHCount.J, RHCount.D, RHCount.P, RHCount.A, C0, h]
  ring
theorem universal_endpoint (d u : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 5/6)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) : E d u ≤ 0 := by
  have hjl := RHCount.J_lower d u hd0 hd1 hu0 hu1
  have hj : 0 < RHCount.J d u := by linarith
  have hq := Q_nonneg d (1/2-u) (by linarith)
  rw [exponent_identity d u (ne_of_gt hj)] at hq
  have he : 0 ≤ -E d u := nonneg_of_mul_nonneg_right hq (by positivity)
  linarith
lemma boundary_identity : boundary = 11/12-ell/4 := by unfold boundary ell; ring
lemma critical_quadratic : 288*dc^2-588*dc+185 = 0 := by
  unfold dc
  ring_nf
  simp only [s_sq]
  ring
lemma critical_range : (3/8 : ℝ) < dc ∧ dc < 5/6 := by
  obtain ⟨hl, hu⟩ := s_bounds
  unfold dc
  constructor <;> linarith
lemma critical_count : R dc (1/2) = 2/3 := by
  have hj : RHCount.J dc (1/2) ≠ 0 := by
    have hh := RHCount.J_lower dc (1/2) (by linarith [critical_range.1])
      (le_of_lt critical_range.2) (by norm_num) (by norm_num)
    linarith
  unfold R
  field_simp [hj]
  unfold RHCount.J RHCount.P RHCount.D RHCount.A dc
  ring_nf
  simp only [s_sq]
  ring
lemma critical_endpoint : E dc (1/2) = 0 := by
  unfold E
  rw [critical_count]
  simp only [C0, dc, b, ell, h]
  ring_nf
  simp only [s_sq]
  ring
lemma gate_b_positive : 0 < b := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [b]
  linarith
lemma gate_x_minus_ell : ell < x := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [x, b, ell]
  linarith
lemma gate_y_minus_ell : ell < y := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, b, ell]
  linarith
lemma gate_ell_positive : 0 < ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [ell]
  linarith
lemma gate_h_positive : 0 < h := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_one_minus_three_ell : 3*ell < 1 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [ell]
  linarith
lemma gate_ell_below_one_fifth : ell < 1/5 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [ell]
  linarith
lemma gate_gram_uniform : 0 < y-ell-11*b/6 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, b, ell]
  linarith
lemma gate_supply : h/5 < ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_five_ell_minus_h : h < 5*ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_floor_saving : 0 < -C0-(1/2+3*ell/2)*(1/50) := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [C0, b, ell]
  linarith
lemma gate_intermediate_floor : 0 < -((225*ell+50-75*b)*(1/50)+78*ell-49*b-73)/300 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [b, ell]
  linarith
lemma gate_intermediate_top : 0 < -((225*ell+50-75*b)*(5/6)+78*ell-49*b-73)/300 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [b, ell]
  linarith
lemma gate_small_saving : 0 < y/2-13*h/75-2/100 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, h, b, ell]
  linarith
lemma gate_small_transport : 0 < y/2-13*h/75-2/100-(7/8-boundary) := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, h, b, ell, boundary]
  linarith
lemma gate_principal_y : 0 < y/20 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, b, ell]
  linarith
lemma gate_principal_h : 0 < h/600 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_boundary_domain : 43/50 < boundary := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [boundary]
  linarith
lemma gate_v1_improvement : boundary < 34999/40000 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [boundary]
  linarith
def w0 : ℝ := (4+18*dc)/(9+18*dc)
def wK : ℝ := 2/(9+18*dc)
def wH : ℝ := 3/(9+18*dc)
lemma dual_den_pos : 0 < 9+18*dc := by linarith [critical_range.1]
lemma weights_pos : 0 < w0 ∧ 0 < wK ∧ 0 < wH := by
  have hh := critical_range.1
  have hd := dual_den_pos
  unfold w0 wK wH
  constructor
  · positivity
  constructor <;> positivity
lemma dual_identity (M l B : ℝ) :
    w0*(B-(5/6+M/12-l/6))+
    wK*(B-(1/3+7*M/12+l/3))+
    wH*(B-(1+dc-(1+dc)*M/2+dc*l)) = B-boundary := by
  unfold w0 wK wH
  field_simp [ne_of_gt dual_den_pos]
  unfold dc boundary
  ring_nf
  simp only [s_sq]
  ring
/-- Exact lower obstruction for the three necessary scalar majorants;
this is not a lower bound for the actual arithmetic energy. -/
theorem closure_obstruction (M l B : ℝ)
    (h0 : 5/6+M/12-l/6 ≤ B)
    (hK : 1/3+7*M/12+l/3 ≤ B)
    (hH : 1+dc-(1+dc)*M/2+dc*l ≤ B) : boundary ≤ B := by
  obtain ⟨hp0, hpK, hpH⟩ := weights_pos
  have hsum : 0 ≤ w0*(B-(5/6+M/12-l/6))+
      wK*(B-(1/3+7*M/12+l/3))+
      wH*(B-(1+dc-(1+dc)*M/2+dc*l)) := by positivity
  rw [dual_identity] at hsum
  linarith
lemma count_as_long (d u : ℝ) : R d u = RHCount.long d (RHCount.t d u) := by
  simp only [R, RHCount.long, RHCount.t]
  ring
/-- At the critical bin, every cutoff has count envelope at least 2/3. -/
theorem critical_count_minimax (t : ℝ) :
    (2/3 : ℝ) ≤ max (RHCount.short dc (1/2) t) (RHCount.long dc t) := by
  rw [← critical_count, count_as_long]
  exact RHCount.balance_is_minimax dc (1/2) t
    (by linarith [critical_range.1]) (le_of_lt critical_range.2)
    (by norm_num) (by norm_num)
/-- The three lower scalar faces are all attained at the proposed geometry. -/
theorem scalar_faces_attained :
    5/6+(1-ell)/12-ell/6 = boundary ∧
    1/3+7*(1-ell)/12+ell/3 = boundary ∧
    1+dc-(1+dc)*(1-ell)/2+dc*ell = boundary := by
  simp only [dc, ell, boundary]
  constructor
  · ring
  constructor
  · ring
  · ring_nf
    simp only [s_sq]
    ring
/-- Boundary optimum of the explicitly listed three-face scalar relaxation. -/
theorem scalar_optimum :
    (∀ M l B : ℝ, 5/6+M/12-l/6 ≤ B →
      1/3+7*M/12+l/3 ≤ B →
      1+dc-(1+dc)*M/2+dc*l ≤ B → boundary ≤ B) ∧
    (5/6+(1-ell)/12-ell/6 ≤ boundary ∧
      1/3+7*(1-ell)/12+ell/3 ≤ boundary ∧
      1+dc-(1+dc)*(1-ell)/2+dc*ell ≤ boundary) := by
  exact ⟨closure_obstruction, le_of_eq scalar_faces_attained.1,
    le_of_eq scalar_faces_attained.2.1, le_of_eq scalar_faces_attained.2.2⟩
lemma signal_matching : x/2+b/12 = boundary-(4+b)/6 := by
  simp only [x, ell, b, boundary]
  ring

lemma s_cube : s^3 = 921*s := by
  calc
    s^3 = s^2*s := by ring
    _ = 921*s := by rw [s_sq]
lemma disc_pos (v : ℝ) (hv : 0 < v) : 0 < disc v := by
  have hc1 := disc_coeff_1_pos
  have hc2 := disc_coeff_2_pos
  have hc3 := disc_coeff_3_pos
  have hc4 := disc_coeff_4_pos
  unfold disc
  positivity
lemma Q_at_zero (d : ℝ) : Q d 0 = Ac 0*(d-dc)^2 := by
  simp only [Q, Ac, C0, dc, h, b, ell]
  ring_nf
  simp only [s_sq, s_cube]
  ring
theorem Q_zero_iff (d v : ℝ) (hv : 0 ≤ v) :
    Q d v = 0 ↔ v = 0 ∧ d = dc := by
  constructor
  · intro hq
    have hv0 : v = 0 := by
      by_contra hn
      have hd := disc_pos v (lt_of_le_of_ne hv (Ne.symm hn))
      have hh := complete_square d v
      rw [hq, mul_zero] at hh
      nlinarith [sq_nonneg (2*Ac v*d+Dc v)]
    subst v
    rw [Q_at_zero] at hq
    have ha := Ac_pos 0 (by norm_num)
    have hdsq : (d-dc)^2 = 0 :=
      (mul_eq_zero.mp hq).resolve_left (ne_of_gt ha)
    exact ⟨rfl, by nlinarith [hdsq]⟩
  · rintro ⟨rfl, rfl⟩
    rw [Q_at_zero]
    ring
theorem endpoint_equality_iff (d u : ℝ) (hu1 : u ≤ 1/2)
    (hj : RHCount.J d u ≠ 0) : E d u = 0 ↔ u = 1/2 ∧ d = dc := by
  constructor
  · intro he
    have hq : Q d (1/2-u) = 0 := by rw [exponent_identity d u hj, he]; ring
    obtain ⟨hu, hd⟩ := (Q_zero_iff d (1/2-u) (by linarith)).mp hq
    exact ⟨by linarith, hd⟩
  · rintro ⟨rfl, rfl⟩
    exact critical_endpoint

#print axioms endpoint_equality_iff
#print axioms critical_count_minimax
#print axioms scalar_optimum
#print axioms signal_matching
#print axioms universal_endpoint
#print axioms critical_endpoint
#print axioms critical_count
#print axioms closure_obstruction
#print axioms gate_v1_improvement
end
end RHV2
