import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing
import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

/-! Recover exactly the original paper's seven-eighths supremum bound from
its actual upstream nonvanishing theorem. This does not assert the extension. -/
namespace RHZeroFreeExtension.ActualOriginalBoundary
noncomputable section
open OAI.SevenEighths HeckeFamily HeckeZeroSupremum

theorem beta_le_seven_eighths : beta ≤ (7 / 8 : ℝ) := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · obtain ⟨chi, s, _hpositive, hpole, hz, rfl⟩ := hx
    by_contra hn
    apply (LFunction_ne_zero_of_seven_eighths_lt_re chi (lt_of_not_ge hn) ?_) hz
    rintro ⟨hc, hs⟩
    rcases hpole with h | h
    · exact h hs
    · exact h hc

#print axioms beta_le_seven_eighths
end
end RHZeroFreeExtension.ActualOriginalBoundary
