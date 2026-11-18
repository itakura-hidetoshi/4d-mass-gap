import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2TwoModeFiniteCylinderTopOrthogonalV5_PZ37AMW
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTimeOneOSVarianceLowerBoundV5_PZ37ANL
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANM — original physical two-mode vacuum overlap obstruction

AMW supplies an actual original physical Gauss-law two-mode top-orthogonal
excitation, and ANL gives the original beta-zero Wilson OS quadratic lower
bound when its zeroth-mode coefficient is nonzero. These are different
Hilbert/OS objects and are not identified here.

This leaf proves that the FIRST physical Wilson mode is the genuine Haar
constant-one Gauss vector, and that the canonical nonnegative normalized
physical top eigenvector has strictly positive overlap with it. Consequently
whether a nonzero zeroth coefficient can occur in the true top-orthogonal
two-mode span is EXACTLY determined by the unproved overlap between the
same top vector and the original first excited Wilson mode.

An existential physical excitation is not silently promoted to an OS nonzero
class. No physical beta-positive overlap or continuum mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANM_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANM_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANM_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANM_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANM_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ37ANM_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact first native Gauss-law Wilson mode, not an abstract chosen
vector, is the ORIGINAL physical constant-one Haar state. -/
theorem p4Q2PZ37ANM_actualModeZero_eq_physicalConstant
    (H : ℕ) :
    p4Q2PZ37AMU_actualPhysicalGaussMode H 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let ν := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let T := p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
  let hMP : MeasurePreserving T μ ν :=
    p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2
  apply Subtype.ext
  change
    (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2)
      (specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 0) =
    Lp.const 2 μ (1 : ℝ)
  rw [p4Q2PZ37ANI_originalWilsonHaarGramSchmidtModeZero_eq_constOne]
  apply Lp.ext
  have hComp :
      (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2)
          (Lp.const 2 ν (1 : ℝ)) =ᵐ[μ]
        (Lp.const 2 ν (1 : ℝ)) ∘ T := by
    change Lp.compMeasurePreserving T hMP (Lp.const 2 ν (1 : ℝ)) =ᵐ[μ] _
    exact Lp.coeFn_compMeasurePreserving _ hMP
  have hSrc :
      (Lp.const 2 ν (1 : ℝ)) =ᵐ[ν] (fun _ => (1 : ℝ)) := by
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (μ := ν) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))
  have hPull :
      ((Lp.const 2 ν (1 : ℝ)) ∘ T) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    exact hMP.quasiMeasurePreserving.ae_eq hSrc
  have hDest :
      (Lp.const 2 μ (1 : ℝ)) =ᵐ[μ] (fun _ => (1 : ℝ)) := by
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (μ := μ) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))
  exact (hComp.trans hPull).trans hDest.symm

/-- The true normalized physical top vector has strictly positive overlap
with the literal zeroth Wilson Gram--Schmidt mode, for all beta >= 0. -/
theorem p4Q2PZ37ANM_originalPhysicalTop_inner_modeZero_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 0) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hNonnegative :
      ∀ᵐ A ∂μ, 0 ≤ (Ω : Lp ℝ 2 μ) A := by
    simpa only [Ω, μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H 2 (by norm_num) beta hbeta)
  have hNorm : ‖(Ω : Lp ℝ 2 μ)‖ = 1 := by
    simpa only [Ω] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
        H 2 (by norm_num) beta hbeta)
  have hMean : 0 < ∫ A, (Ω : Lp ℝ 2 μ) A ∂μ :=
    realL2_integral_pos_of_ae_nonnegative_norm_one
      (Ω : Lp ℝ 2 μ) hNonnegative hNorm
  have hEq :
      inner ℝ Ω (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
        ∫ A, (Ω : Lp ℝ 2 μ) A ∂μ := by
    calc
      inner ℝ Ω (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
          inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) Ω :=
        real_inner_comm _ _
      _ = ∫ A, (Ω : Lp ℝ 2 μ) A ∂μ := by
        change inner ℝ (Lp.const 2 μ (1 : ℝ)) (Ω : Lp ℝ 2 μ) = _
        exact realL2_inner_const_one_eq_integral _
  rw [p4Q2PZ37ANM_actualModeZero_eq_physicalConstant]
  change 0 <
    inner ℝ Ω (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  rw [hEq]
  exact hMean

/-- Sharp algebraic two-mode coefficient obstruction: once the physical
vacuum overlaps mode zero nontrivially, a top-orthogonal combination with a
nonzero zeroth coefficient exists exactly when the vacuum overlaps mode one.
No abstract orthogonal-vector existence assumption is needed. -/
theorem p4Q2PZ37ANM_twoMode_nonzero_c0_iff_secondOverlap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω v0 v1 : E) (hv0 : ‖v0‖ = 1)
    (h01 : inner ℝ v0 v1 = 0)
    (ha : inner ℝ Ω v0 ≠ 0) :
    (∃ c0 c1 : ℝ,
      c0 ≠ 0 ∧
      c0 • v0 + c1 • v1 ≠ 0 ∧
      inner ℝ Ω (c0 • v0 + c1 • v1) = 0) ↔
      inner ℝ Ω v1 ≠ 0 := by
  constructor
  · rintro ⟨c0, c1, hc0, -, horth⟩ hbzero
    rw [inner_add_right, real_inner_smul_right,
      real_inner_smul_right, hbzero] at horth
    have hz : c0 * inner ℝ Ω v0 = 0 := by
      simpa only [mul_zero, add_zero] using horth
    rcases mul_eq_zero.mp hz with hz0 | hza
    · exact hc0 hz0
    · exact ha hza
  · intro hb
    let a : ℝ := inner ℝ Ω v0
    let b : ℝ := inner ℝ Ω v1
    have hb0 : b ≠ 0 := hb
    have hself : inner ℝ v0 v0 = 1 := by
      rw [real_inner_self_eq_norm_sq, hv0]
      norm_num
    have hval : inner ℝ v0 (b • v0 + (-a) • v1) = b := by
      rw [inner_add_right, real_inner_smul_right,
        real_inner_smul_right, hself, h01]
      ring
    have hwne : b • v0 + (-a) • v1 ≠ 0 := by
      intro hw
      rw [hw] at hval
      have hzero : b = 0 := by
        have hz : (0 : ℝ) = b := by simpa using hval
        exact hz.symm
      exact hb0 hzero
    have horth : inner ℝ Ω (b • v0 + (-a) • v1) = 0 := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      dsimp [a, b]
      ring
    exact ⟨b, -a, hb0, hwne, horth⟩

/-- For the actual original physical Wilson top eigenspace, the exact
necessary AND sufficient obstruction for a top-orthogonal TWO-mode
physical vector with nonzero coefficient c0 is the unproved original
vacuum–first-excited-mode overlap. No such overlap is asserted here. -/
theorem p4Q2PZ37ANM_originalPhysicalTwoMode_c0_ne_zero_iff_vacuumModeOneOverlap
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∃ c0 c1 : ℝ,
      c0 ≠ 0 ∧
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ≠ 0 ∧
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta) ↔
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ≠ 0 := by
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let v0 := p4Q2PZ37AMU_actualPhysicalGaussMode H 0
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have ho := p4Q2PZ37AMU_actualPhysicalGaussMode_orthonormal H
  have hv0 : ‖v0‖ = 1 := by simpa only [v0] using ho.1 0
  have h01 : inner ℝ v0 v1 = 0 := by
    simpa only [v0, v1] using ho.inner_eq_zero (by decide : (0 : ℕ) ≠ 1)
  have ha : inner ℝ Ω v0 ≠ 0 :=
    ne_of_gt (p4Q2PZ37ANM_originalPhysicalTop_inner_modeZero_pos H beta hbeta)
  have hiff := p4Q2PZ37ANM_twoMode_nonzero_c0_iff_secondOverlap
    Ω v0 v1 hv0 h01 ha
  have htop :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H 2 (by norm_num) beta hbeta = ℝ ∙ Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_nonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  constructor
  · rintro ⟨c0, c1, hc0, hne, hmem⟩
    apply hiff.mp
    refine ⟨c0, c1, hc0, hne, ?_⟩
    change c0 • v0 + c1 • v1 ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H 2 (by norm_num) beta hbeta)ᗮ at hmem
    rw [htop] at hmem
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := Ω) (v := c0 • v0 + c1 • v1)).mp hmem
  · intro hb
    obtain ⟨c0, c1, hc0, hne, horth⟩ := hiff.mpr hb
    refine ⟨c0, c1, hc0, hne, ?_⟩
    change c0 • v0 + c1 • v1 ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H 2 (by norm_num) beta hbeta)ᗮ
    rw [htop]
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ) (u := Ω) (v := c0 • v0 + c1 • v1)).mpr horth

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANM_actualModeZero_eq_physicalConstant
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANM_originalPhysicalTop_inner_modeZero_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANM_twoMode_nonzero_c0_iff_secondOverlap
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANM_originalPhysicalTwoMode_c0_ne_zero_iff_vacuumModeOneOverlap
