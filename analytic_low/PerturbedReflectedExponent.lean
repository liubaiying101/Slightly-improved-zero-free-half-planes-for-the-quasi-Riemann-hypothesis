import OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent

/-! Generalizes the original reflected exponent estimate to arbitrary total
selected length L. The expression here is the authentic upstream
InverseTerminalWidths.reflectedExponent, not a replacement energy definition.
This is the exponent seam only; actual reflection/aggregation remains upstream. -/
namespace OAI.SevenEighths.ProbeLowReflected
open InverseTerminalWidths

theorem perturbed_compensated_reflected_exponent_with_length
    (L d ell0 O0 H A0 N0 S0 B0 za v ell el theta epsilon : ℝ)
    (hd : 0 ≤ d) (heps : 0 ≤ epsilon)
    (hO : -epsilon ≤ O0) (hH : H ≤ (1-L-2*d)-O0+epsilon)
    (hA : 2*A0 ≤ O0+epsilon) (hN : 0 ≤ N0) (hNA : N0 ≤ A0)
    (hS : 0 ≤ S0) (hB : 0 ≤ B0)
    (hell : ell0 ≤ L-d+epsilon) (hz : za ≤ ell0+epsilon)
    (hv : -epsilon ≤ v) (hl : -epsilon ≤ ell) (he : -epsilon ≤ el)
    (htheta : |theta| ≤ epsilon)
    (hret : v+3*ell+el ≤ 2*H+2*A0+2*za-1-ell0-theta-N0-3*B0+epsilon) :
    reflectedExponent O0 H S0 B0 za v ell el
      (2*H+2*A0+2*za-1-ell0-theta-N0-3*B0) ≤
        (1-L-2*d) + max (d+5*L-1) 0 / 4 + 40*epsilon := by
  let Td := 2*H+2*A0+2*za-1-ell0-theta-N0-3*B0
  have htlo : -epsilon ≤ theta := (abs_le.mp htheta).1
  have hthi : theta ≤ epsilon := (abs_le.mp htheta).2
  have hTd : Td ≤ H-3*d+6*epsilon := by dsimp [Td]; linarith
  have hcol : v+ell ≤ H+10*epsilon := by dsimp [Td] at hTd; linarith
  have hmax : max H (v+ell) ≤ H+10*epsilon := max_le (by linarith) hcol
  have hk := le_max_left (0 : ℝ) (Td-v-3*ell-el)
  have hc0 := le_max_right (d+5*L-1) (0 : ℝ)
  have hc1 := le_max_left (d+5*L-1) (0 : ℝ)
  by_cases hu : hybridSaving v za = za
  · unfold reflectedExponent
    rw [hu]
    change O0/2+max H (v+ell)-S0-B0+za-za-ell-2*el/3-
      max 0 (Td-v-3*ell-el)/2 ≤ _
    linarith
  · have hhalf := hybrid_half_with_error hv heps hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*epsilon/12 ≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el) = Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O0 H S0 B0 za v ell el Td ≤
        O0/2+H-S0-B0+za-Td/4+(10+17/12)*epsilon := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O0 H S0 B0 za v ell el Td ≤ _
    apply hbound.trans
    dsimp [Td]
    linarith

end OAI.SevenEighths.ProbeLowReflected
