import RHZeroFreeExtension.analytic_high.V2FinalData
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono


noncomputable section
open scoped Classical BigOperators
open Filter
namespace RHZeroFreeExtension.AnalyticHigh.V2
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
   ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1/200:ℝ) ≤ d  →  d ≤ 7/8  →  51/100 < a  →  a ≤ 1  → 
    ( ∀ u∈rows,u.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm u  ∧ 
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0  ∧  rowNorm u ≤ Z^(d-D.t))  → 
     ∀ i : ℕ, ∀ z : ℂ,z.re=17/50  →  |z.im| ≤ height  → 
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z (0:ℝ)
      (if 2*a-1 ≤ 5/6 then counts.cB else counts.cH)
      (if 2*a-1 ≤ 5/6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBound.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : CountParameters F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0 ≤ Z) (h : SourceMomentBound F counts η Z τ C height) (hC : C ≤ C') :
    SourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z (0:ℝ) _ _ C C' height D.t
    hZ hC (h rows d a hd hd' ha ha' hrows i z hz hzh)

def RawMomentInput : Prop :=
   ∀ _hβ : (RHV2.boundary:ℝ) < HeckeZeroSupremum.beta,
     ∀ D : HighData (HeckeZeroSupremum.beta-RHV2.boundary), ∀ F : SourceData D,
     ∀ counts : CountParameters F.modulus ⊤ D.t,
     ∃ J : ℝ,0 ≤ J  ∧   ∀ η : Character, ∃ C : ℝ,0 < C  ∧ 
       ∀ τ : ℝ,0 < τ  →  τ ≤ 1  →   ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

lemma polynomial_height_absorption (C Z τ J t : ℝ)
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (hbudget : 2*τ*(1+J) ≤ t) :
    C*(1+Z^(2*τ))^J ≤ (C*2^J)*Z^t := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hscale : 1 ≤ Z^(2*τ) := Real.one_le_rpow hZ (by positivity)
  calc
    _ ≤ C*(2*Z^(2*τ))^J := by gcongr;linarith
    _=(C*2^J)*Z^(2*τ*J) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
      ring
    _ ≤ (C*2^J)*Z^t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem raw_input_chosen_height (h : RawMomentInput) (hβ : (RHV2.boundary:ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-RHV2.boundary)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
     ∃ τ : ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200:ℝ)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η : Character, ∃ C : ℝ,0 < C  ∧   ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := h hβ D F counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩ := D.height_choice J hJ
  have htau1 : τ ≤ 1 := by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith) (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ hτJ)

def ChosenMomentInput : Prop :=
  ∀ _hβ : RHV2.boundary < HeckeZeroSupremum.beta,
    ∃ D : HighData (HeckeZeroSupremum.beta-RHV2.boundary), ∃ F : SourceData D,
    ∃ counts : CountParameters F.modulus ⊤ D.t,
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput : Prop :=
  ∀ _hβ : RHV2.boundary < HeckeZeroSupremum.beta,
    ∃ mesh : ℝ → ℝ, (∀ t : ℝ, 0 < t → 0 < mesh t) ∧
      ∀ D : HighData (HeckeZeroSupremum.beta-RHV2.boundary),
      (∀ j, D.ell j ≤ mesh D.t/200) →
      ∀ F : SourceData D, ∀ counts : CountParameters F.modulus ⊤ D.t,
      ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
          SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h : FineMomentInput) : ChosenMomentInput := by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩ := h hβ
  obtain ⟨D,hD⟩ := exists_high_data_fine (HeckeZeroSupremum.beta-RHV2.boundary) (by linarith) mesh hmesh
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

end RHZeroFreeExtension.AnalyticHigh.V2

end


#print axioms RHZeroFreeExtension.AnalyticHigh.V2.raw_input_chosen_height
