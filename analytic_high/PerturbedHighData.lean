import OAI.NumberTheory.DirichletL.ParametersDetectorScales
import geometry.SlotLengths


noncomputable section
open scoped BigOperators
namespace RHZeroFreeExtension.AnalyticHigh
open OAI.SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N → ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t < Δ/4
  t_small : t ≤ 1/100000000
  slots_even : Even N
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=5003/30000
  slots_bounds :  ∀ j,0 < ell j  ∧  (7/8)*rmin ≤ ell j  ∧  ell j ≤ (1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e < 1/1000
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  detector_budget : 288*e+8*κ+2*cost ≤ ε/2
  phase_budget : 8*e*t+κ ≤ ε
  count_budget : 159*ε+t+t+7*t ≤ 1/32
  central_budget : (16253/20000)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+(5003/30000)*t)+(t+t+t)+t ≤ 19/320000
  geometric_budget : sigma+8*e+t/8 ≤ 39337/500000
  principal_budget : sigma+t/8 ≤ 17/48000
  window_budget : sigma+e ≤ (34999/40000)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+(5003/30000)*t+t/8+sigma ≤ 1093/192000
  high_saving : sigma+t/8+t/8 ≤ t
  height_choice :  ∀ J : ℝ,0 ≤ J  →   ∃ τ : ℝ,0 < τ  ∧  τ < (1/200)/2  ∧ 
    4*τ < (1/200)*cost  ∧  τ < t  ∧  2*τ*(1+J) ≤ t  ∧  τ*(2+4*eps) < t

theorem exists_high_data_fine (Δ : ℝ) (hΔ : 0 < Δ) (mesh : ℝ → ℝ)
    (hmesh : ∀ t : ℝ,0 < t → 0 < mesh t) :  ∃ D : HighData Δ, ∀ j,D.ell j ≤ mesh D.t/200 := by
  let t : ℝ := min (Δ/8) (1/1000000000000)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htΔ : t < Δ/4 := by have hh:=min_le_left (Δ/8) (1/1000000000000:ℝ);dsimp [t];linarith
  have htTiny : t ≤ 1/1000000000000 := min_le_right _ _
  have ht1 : t ≤ 1/100000000 := by linarith
  let L : ℝ := min t (mesh t)/200
  have hL : 0 < L := div_pos (lt_min ht (hmesh t ht)) (by norm_num)
  obtain ⟨N,hN,hEven,ell,hell,hbounds,hsum⟩ :=
    RHSlotLengths.exists_even_distinct_slot_lengths (5003/30000) L (by norm_num) hL
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,_hj,hminj⟩ := Finset.exists_min_image Finset.univ ell hne
  let rmin : ℝ := ell j/(2*(7/8))
  have hr : 0 < rmin := div_pos (hbounds j).1 (by norm_num)
  have hlo (k : Fin N) : (7/8:ℝ)*rmin ≤ ell k := by
    have hh := hminj k (Finset.mem_univ k)
    have hi : (7/8:ℝ)*rmin=ell j/2 := by dsimp [rmin];ring
    rw [hi];linarith [(hbounds j).1]
  have hup (k : Fin N) : ell k ≤ t/200 := by
    exact (hbounds k).2.le.trans ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 200)).mpr (min_le_left _ _))
  have hfine (k : Fin N) : ell k ≤ mesh t/200 := by
    exact (hbounds k).2.le.trans ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 200)).mpr (min_le_right _ _))
  let small := t/((N:ℝ)+2000)
  have hsmall : 0 < small := div_pos ht (by positivity)
  have hst : small ≤ t/((N:ℝ)+2000) := le_rfl
  have hst0 : small ≤ t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0 < eps := by dsimp [eps];positivity
  have hepss : eps ≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps ≤ 1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ (show 0 < (N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000*e ≤ t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t/2 := min_le_left _ _
  have hsell : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_small:=ht1,slots_even:=hEven,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun k=>⟨(hbounds k).1,hlo k,by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hup k⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=by linarith only [hεa,hst0,htTiny]
    central_budget:=by linarith only [hεa,hst0,het,he8,htTiny]
    geometric_budget:=by linarith only [hst2, het, htTiny]
    principal_budget:=by linarith only [hst2, htTiny]
    window_budget:=by change sigma+e ≤ (34999/40000)*ellMin;linarith only [hsell, heell, hmin]
    floor_budget:=by linarith only [hst2, het, he8, htTiny]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ ≤ (1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0 ≤ τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
        by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
        by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · exact hfine

theorem fine_slot_widths {gap : ℝ} (D : HighData gap) (mesh : ℝ → ℝ)
    (_hmesh : 0 < mesh D.t) (hfine : ∀ j, D.ell j ≤ mesh D.t/200)
    (d : ℝ) (hd : (1/200 : ℝ) ≤ d) (j : Fin D.N) :
    0 < D.ell j/d ∧ D.ell j/d ≤ mesh D.t := by
  have hd0 : 0 < d := by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0, (div_le_iff₀ hd0).mpr ?_⟩
  have hh := hfine j
  nlinarith

end RHZeroFreeExtension.AnalyticHigh
end

#print axioms RHZeroFreeExtension.AnalyticHigh.exists_high_data_fine

#print axioms RHZeroFreeExtension.AnalyticHigh.fine_slot_widths
