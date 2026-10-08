import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI.SevenEighths.ProbePhysical

lemma perturbed_compensation_factor (L Z R c d : ℝ)
    (hL : L≤1/5) (hZ : 1≤Z) (hc : 0<c) (hd : 0≤d)
    (hR : c*Z^d≤R) :
    R^(-(1/2:ℝ))*Z^(max (d+5*L-1) 0/8)≤c^(-(1/2:ℝ)) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hb : 0<c*Z^d := mul_pos hc (Real.rpow_pos_of_pos hz _)
  have hm : max (d+5*L-1) 0/8≤d/2 := by
    have hh : max (d+5*L-1) 0≤d := max_le (by linarith) hd
    linarith
  calc
    _≤(c*Z^d)^(-(1/2:ℝ))*Z^(d/2) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow_of_nonpos hb hR (by norm_num)
      · exact Real.rpow_le_rpow_of_exponent_le hZ hm
      · positivity
      · positivity
    _=c^(-(1/2:ℝ)) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hz.le _),←Real.rpow_mul hz.le]
      rw [mul_assoc,←Real.rpow_add hz]
      have he : d*(-(1/2:ℝ))+d/2=0 := by ring
      rw [he,Real.rpow_zero,mul_one]

end OAI.SevenEighths.ProbePhysical
