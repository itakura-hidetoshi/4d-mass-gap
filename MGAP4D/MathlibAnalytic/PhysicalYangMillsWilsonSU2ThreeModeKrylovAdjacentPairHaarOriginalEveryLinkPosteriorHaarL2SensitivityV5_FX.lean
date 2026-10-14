import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEveryLinkNormalizedPosteriorSensitivityV5_FS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalConditionalPosteriorDensityFloorV5_FK
import Mathlib.Tactic

/-!
# P4-Q2-FX: genuine Wilson posterior left-link sensitivity survives SU(2) Haar integration

FS proves that for EVERY true physical SU(2) spatial link e, at fixed beta>0
and any right-boundary environment, the TWO normalized, interacting Wilson
posterior conditional densities obtained at left boundaries A0=identity and
A1=pi-rotated AT e cannot agree at both right insertions g=1,R(pi).

The original posterior densities are continuous and normalized against
real SU(2) compact Haar, which has positive mass on every nonempty open
set. Therefore this TRUE conditional-law left sensitivity survives
integration in its RIGHT Haar candidate-link variable:

  ∫_g (p_beta,e(g | A0, B_off) -
        p_beta,e(g | A1, B_off))^2 dHaar(g) > 0.

This is NOT a scalar witness at Haar-null points: the full right-link
Haar L² separation is strictly positive at EVERY actual link, in every
finite volume, every right environment. No surrogate posterior,
Dobrushin, source-dependent FF response, quantitative volume-uniform
L² floor or continuum Yang--Mills gap is claimed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 650000

local instance p4Q2FX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2FX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2FX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2FX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2FX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2FX_haarOpenPos :
    Measure.IsOpenPosMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

/-- Literal source-boundary dependence of the original fully normalized,
interacting Wilson posterior one-link conditional density, in the right
SU(2) normalized compact Haar L² squared norm. -/
noncomputable def p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∫ g : Matrix.specialUnitaryGroup (Fin 2) ℂ,
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e g -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
        H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g) ^ 2
    ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)

/-- All true original Wilson posterior links remain genuinely
left-boundary-sensitive IN HAAR L², not only at a two-point test.
Positivity is qualitative (may depend on H,e,right,beta). -/
theorem p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 < p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
      H beta (le_of_lt hbeta) right e := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let P0 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta (le_of_lt hbeta)
      (originalWilsonExplicitIdentityBoundary H) right e
  let P1 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta (le_of_lt hbeta)
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  let F : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    fun g => (P0 g - P1 g) ^ 2
  have hCont0 : Continuous P0 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta (le_of_lt hbeta)
          (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (originalWilsonExplicitIdentityBoundary H) right e)
  have hCont1 : Continuous P1 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta (le_of_lt hbeta)
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta (le_of_lt hbeta)
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  have hCont : Continuous F := (hCont0.sub hCont1).pow 2
  have hInt : Integrable F μ :=
    hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDifferent :
      P0 (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) ≠ P1 1 ∨
        P0 (specialUnitaryTwoRotation Real.pi) ≠
          P1 (specialUnitaryTwoRotation Real.pi) := by
    exact p4Q2FS_originalSU2EveryLinkTruePosteriorDensity_leftSensitive
      H beta hbeta right e
  obtain ⟨g, hNotEq⟩ :
      ∃ g : Matrix.specialUnitaryGroup (Fin 2) ℂ, P0 g ≠ P1 g := by
    rcases hDifferent with hOne | hRot
    · exact ⟨1, hOne⟩
    · exact ⟨specialUnitaryTwoRotation Real.pi, hRot⟩
  have hFNonzero : F g ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hNotEq)
  have hSupportOpen : IsOpen (Function.support F) := by
    change IsOpen (F ⁻¹' ({0} : Set ℝ)ᶜ)
    exact isClosed_singleton.isOpen_compl.preimage hCont
  have hSupportNonempty : (Function.support F).Nonempty :=
    ⟨g, hFNonzero⟩
  have hSupportPositive : 0 < μ (Function.support F) :=
    hSupportOpen.measure_pos μ hSupportNonempty
  change 0 < ∫ g, F g ∂μ
  rw [integral_pos_iff_support_of_nonneg]
  · exact hSupportPositive
  · intro x
    exact sq_nonneg _
  · exact hInt

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq_pos
