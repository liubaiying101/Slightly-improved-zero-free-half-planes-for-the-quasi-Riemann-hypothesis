import geometry.V2AnalyticGeometry
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison

/-! Actual double-residue normalization for the v2 physical probe. The pole
is still 1/6. Changing b changes the signal intercept to -(4+b)/6. -/
namespace RHV2
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Complex
open OAI OAI.SevenEighths
open HeckeFamily PrincipalSlotEstimate ProbePhysical HeckeSignal
open PrincipalSignalComparison PrincipalMellinResidues
variable {kappa iota : Type*}

def slotResidue (chi : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset kappa) (T : kappa → Finset iota) (w Q : kappa → iota → ℝ)
    (A eta : kappa → iota → ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
    (Z : ℂ)^(((a : ℂ)+t*I)-(((4+b)/6 : ℝ) : ℂ))*
      Complex.exp ((((a : ℂ)+t*I)-5/6)^2)*H ((a : ℂ)+t*I)/
      LFunction chi ((a : ℂ)+t*I)*slotRatio S T w Q A eta ((a : ℂ)+t*I)

theorem source_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z^x : ℝ) : ℂ)^(1/3 : ℂ)*(Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-ell/6 : ℝ) : ℂ))*
        (Z : ℂ)^(s-(((4+b)/6 : ℝ) : ℂ)) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le x (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  simp only [x]
  push_cast
  ring

theorem normalized_source_double_residue (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (chi : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset kappa) (T : kappa → Finset iota) (w Q : kappa → iota → ℝ)
    (A eta : kappa → iota → ℂ) (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A eta s) :
    (fixedPrincipalResidue M^2/6*
      sourceMultiplier W0 W1 (Z^x) Y Z chi s H B 1 (1/6))/
      (sourceResidueConstant W0 W1 M*
        (Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s-(((4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*
        H 1 (1/6)/LFunction chi s*slotRatio S T w Q A eta s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := source_power_identity hZ s
  have hz : (Z : ℂ)^(((-ell/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M*(sourceResidueConstant W0 W1 M)⁻¹)*
      ((Z : ℂ)^(((-ell/6 : ℝ) : ℂ))*((Z : ℂ)^(((-ell/6 : ℝ) : ℂ)))⁻¹)*
      ((Z : ℂ)^(s-(((4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*
        H 1 (1/6)*(LFunction chi s)⁻¹*
        (slotProduct S T w Q A eta s*(PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem sourceResidueIntegral_normalized (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (chi : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset kappa) (T : kappa → Finset iota)
    (w Q : kappa → iota → ℝ) (A eta : kappa → iota → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0) (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A eta ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M chi a (Z^x) Y Z H B/
      (sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
        slotResidue chi (fun s => H s 1 (1/6)) a Z S T w Q A eta := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral RHV2.slotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat] using
    normalized_source_double_residue W0 W1 M chi Y Z hZ ((a : ℂ)+t*I)
      (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) S T w Q A eta hc (hB t)

#print axioms source_power_identity
#print axioms normalized_source_double_residue
#print axioms sourceResidueIntegral_normalized
end
end RHV2
