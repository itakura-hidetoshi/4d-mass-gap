import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedOneStepGenerator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- A coercive bounded real-Hilbert endomorphism controls the norm of any
bounded right inverse.  The result is phrased without a nontriviality
assumption on the carrier. -/
theorem realContinuousLinearMap_rightInverse_norm_le_inv_of_coercive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (G R : E →L[ℝ] E)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hcoercive : ∀ x : E, gap * ‖x‖ ^ 2 ≤ inner ℝ (G x) x)
    (hGR : G * R = 1) :
    ‖R‖ ≤ gap⁻¹ := by
  have hpoint : ∀ x : E, gap * ‖x‖ ≤ ‖G x‖ := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hinner : inner ℝ (G x) x ≤ ‖G x‖ * ‖x‖ := real_inner_le_norm _ _
      have hmul : gap * ‖x‖ ^ 2 ≤ ‖G x‖ * ‖x‖ :=
        (hcoercive x).trans hinner
      nlinarith
  change ContinuousLinearMap.opNorm R ≤ gap⁻¹
  apply ContinuousLinearMap.opNorm_le_bound
  · exact inv_nonneg.mpr hgap.le
  · intro y
    have happly : G (R y) = y := by
      have h := congrArg (fun A : E →L[ℝ] E => A y) hGR
      simpa using h
    have hbase : gap * ‖R y‖ ≤ ‖y‖ := by
      simpa [happly] using hpoint (R y)
    have hdiv : ‖R y‖ ≤ ‖y‖ / gap :=
      (le_div_iff₀ hgap).2 (by simpa [mul_comm] using hbase)
    simpa [div_eq_inv_mul] using hdiv

/-- A symmetric coercive endomorphism transfers symmetry to any bounded right
inverse. -/
theorem realContinuousLinearMap_rightInverse_inner_symm
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (G R : E →L[ℝ] E)
    (hG : ∀ x y : E, inner ℝ (G x) y = inner ℝ x (G y))
    (hGR : G * R = 1) :
    ∀ x y : E, inner ℝ (R x) y = inner ℝ x (R y) := by
  intro x y
  have hx : G (R x) = x := by
    have h := congrArg (fun A : E →L[ℝ] E => A x) hGR
    simpa using h
  have hy : G (R y) = y := by
    have h := congrArg (fun A : E →L[ℝ] E => A y) hGR
    simpa using h
  calc
    inner ℝ (R x) y = inner ℝ (R x) (G (R y)) := by rw [hy]
    _ = inner ℝ (G (R x)) (R y) := (hG (R x) (R y)).symm
    _ = inner ℝ x (R y) := by rw [hx]

/-- The quadratic form of a right inverse of a symmetric coercive operator is
nonnegative. -/
theorem realContinuousLinearMap_rightInverse_inner_nonneg_of_coercive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (G R : E →L[ℝ] E)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hcoercive : ∀ x : E, gap * ‖x‖ ^ 2 ≤ inner ℝ (G x) x)
    (hGR : G * R = 1)
    (y : E) :
    0 ≤ inner ℝ (R y) y := by
  have hy : G (R y) = y := by
    have h := congrArg (fun A : E →L[ℝ] E => A y) hGR
    simpa using h
  have hlower := hcoercive (R y)
  have hnonneg : 0 ≤ gap * ‖R y‖ ^ 2 :=
    mul_nonneg hgap.le (sq_nonneg _)
  calc
    0 ≤ gap * ‖R y‖ ^ 2 := hnonneg
    _ ≤ inner ℝ (G (R y)) (R y) := hlower
    _ = inner ℝ (R y) (G (R y)) := real_inner_comm _ _
    _ = inner ℝ (R y) y := by rw [hy]

/-- The inverse quadratic form also satisfies the explicit upper Green bound. -/
theorem realContinuousLinearMap_rightInverse_inner_le_inv_mul_norm_sq_of_coercive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (G R : E →L[ℝ] E)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hcoercive : ∀ x : E, gap * ‖x‖ ^ 2 ≤ inner ℝ (G x) x)
    (hGR : G * R = 1)
    (y : E) :
    inner ℝ (R y) y ≤ gap⁻¹ * ‖y‖ ^ 2 := by
  have hR : ‖R‖ ≤ gap⁻¹ :=
    realContinuousLinearMap_rightInverse_norm_le_inv_of_coercive
      G R gap hgap hcoercive hGR
  calc
    inner ℝ (R y) y ≤ ‖R y‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ (‖R‖ * ‖y‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (R.le_opNorm y) (norm_nonneg y)
    _ ≤ (gap⁻¹ * ‖y‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hR (norm_nonneg y))
        (norm_nonneg y)
    _ = gap⁻¹ * ‖y‖ ^ 2 := by ring

local instance osBoundaryExcitationCompletedOneStepGreenSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedOneStepGreenSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedOneStepGreenSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedOneStepGreenSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedOneStepGreenSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedOneStepGreenSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedOneStepGreenSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedOneStepGreenPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The canonical unit represented by the invertible completed one-step
discrete generator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorUnit
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)ˣ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isUnit
    H N hN beta hbeta).unit

/-- The bounded finite-volume Green operator of the completed one-step
discrete generator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  ↑((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorUnit
    H N hN beta hbeta)⁻¹)

/-- The generator followed by its completed Green operator is the identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mul_green
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
          H N hN beta hbeta = 1 := by
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isUnit
      H N hN beta hbeta
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta *
        ↑(hG.unit⁻¹) = 1
  simpa only [hG.unit_spec] using hG.unit.mul_inv

/-- The completed Green operator followed by the generator is also the identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreen_mul_generator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
          H N hN beta hbeta *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta = 1 := by
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isUnit
      H N hN beta hbeta
  change
    ↑(hG.unit⁻¹) *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta = 1
  simpa only [hG.unit_spec] using hG.unit.inv_mul

/-- The completed one-step Green operator satisfies the explicit inverse-gap
operator norm estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_norm_le_gap_inv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)⁻¹ := by
  exact
    realContinuousLinearMap_rightInverse_norm_le_inv_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap_pos
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_lower_bound
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mul_green
        H N hN beta hbeta)

/-- The completed one-step Green operator is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta) := by
  apply continuousLinearMap_isSelfAdjoint_of_inner_symm
  have hG :
      ∀ x y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta,
        inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
              H N hN beta hbeta x) y =
          inner ℝ x
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
              H N hN beta hbeta y) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta)
  exact
    realContinuousLinearMap_rightInverse_inner_symm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta)
      hG
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mul_green
        H N hN beta hbeta)

/-- The completed one-step Green quadratic form is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta u)
      u := by
  exact
    realContinuousLinearMap_rightInverse_inner_nonneg_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap_pos
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_lower_bound
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mul_green
        H N hN beta hbeta)
      u

/-- The completed one-step Green quadratic form is explicitly bounded above by
the inverse finite-volume generator gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_inner_le_gap_inv_mul_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
          H N hN beta hbeta u)
        u ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)⁻¹ * ‖u‖ ^ 2 := by
  exact
    realContinuousLinearMap_rightInverse_inner_le_inv_mul_norm_sq_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap_pos
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_lower_bound
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mul_green
        H N hN beta hbeta)
      u

/-- Audit-visible bounded Green-operator package for the completed finite-volume
one-step excitation generator. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedOneStepGreenOperatorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  generatorMulGreen :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
          H N hN beta hbeta = 1
  greenMulGenerator :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
          H N hN beta hbeta *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta = 1
  greenNormBound :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)⁻¹
  greenSelfAdjoint :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
        H N hN beta hbeta)
  greenQuadraticNonnegative :
    ∀ u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta,
      0 ≤ inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
          H N hN beta hbeta u)
        u
  greenQuadraticUpperBound :
    ∀ u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator
            H N hN beta hbeta u)
          u ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)⁻¹ * ‖u‖ ^ 2

/-- Construct the completed bounded Green-operator package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedOneStepGreenOperatorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedOneStepGreenOperatorPackage
      H N hN beta hbeta :=
  { generatorMulGreen :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mul_green
        H N hN beta hbeta
    greenMulGenerator :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreen_mul_generator
        H N hN beta hbeta
    greenNormBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_norm_le_gap_inv
        H N hN beta hbeta
    greenSelfAdjoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_isSelfAdjoint
        H N hN beta hbeta
    greenQuadraticNonnegative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_inner_nonneg
        H N hN beta hbeta
    greenQuadraticUpperBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGreenOperator_inner_le_gap_inv_mul_norm_sq
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D