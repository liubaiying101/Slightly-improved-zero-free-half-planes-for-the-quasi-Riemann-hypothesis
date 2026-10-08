import OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry

namespace OAI
noncomputable section
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
lemma perturbed_lowLength_bounds (lengthCap : ℝ) {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤lengthCap) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤lengthCap ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤lengthCap-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma perturbed_lowPhysicalScale_source (lengthCap x y : ℝ) (hxy : x+y=1-lengthCap) (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(x)/L) (Z^(y)/L)=
      elementNorm C.generator*Z^(1-lengthCap)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(x)*Z^(y)=Z^(1-lengthCap) := by rw [←Real.rpow_add hZ]; rw [hxy]
  rw [←he]
  ring

lemma perturbed_lowPhysicalScale_nominal_bound (lengthCap x y : ℝ) (hxy : x+y=1-lengthCap) (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(x)/L) (Z^(y)/L)≤
      (elementNorm C.generator/c^2)*Z^(1-lengthCap-2*d) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [perturbed_lowPhysicalScale_source lengthCap x y hxy C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(1-lengthCap)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      have hquot : Z^(1-lengthCap-2*d)=Z^(1-lengthCap)/Z^(2*d) :=
        Real.rpow_sub hZ _ _
      rw [mul_pow,hp,hquot]
      ring


end SevenEighths.ProbePhysical
end
end OAI
