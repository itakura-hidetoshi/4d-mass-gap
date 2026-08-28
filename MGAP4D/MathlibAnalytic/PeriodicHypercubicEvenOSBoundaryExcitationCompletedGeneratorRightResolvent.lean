import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferPositivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- An upper quadratic bound for a bounded real-Hilbert endomorphism becomes a
coercive lower bound for the right spectral shift `lambda I - G`. -/
theorem realContinuousLinearMap_smul_one_sub_inner_lower_bound
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E)
    (upper lambda : ℝ)
    (hupper : ∀ x : E, inner ℝ (G x) x ≤ upper * ‖x‖ ^ 2)
    (u : E) :
    (lambda - upper) * ‖u‖ ^ 2 ≤
      inner ℝ ((lambda • (1 : E →L[ℝ] E) - G) u) u := by
  have hG := hupper u
  change
    (lambda - upper) * ‖u‖ ^ 2 ≤
      inner ℝ (lambda • u - G u) u
  calc
    (lambda - upper) * ‖u‖ ^ 2 =
        lambda * ‖u‖ ^ 2 - upper * ‖u‖ ^ 2 := by ring
    _ ≤ lambda * ‖u‖ ^ 2 - inner ℝ (G u) u :=
      sub_le_sub_left hG _
    _ = inner ℝ (lambda • u - G u) u := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- The right scalar shift `lambda I - G` of a self-adjoint bounded
real-Hilbert endomorphism is self-adjoint. -/
theorem realContinuousLinearMap_smul_one_sub_isSelfAdjoint
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (G : E →L[ℝ] E)
    (hG : IsSelfAdjoint G)
    (lambda : ℝ) :
    IsSelfAdjoint (lambda • (1 : E →L[ℝ] E) - G) := by
  apply continuousLinearMap_isSelfAdjoint_of_inner_symm
  have hSymm : G.toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hG
  intro x y
  change
    inner ℝ (lambda • x - G x) y =
      inner ℝ x (lambda • y - G y)
  rw [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hSymm x y]

/-- In a real normed Banach algebra, the inverse of the affine right shift
`lambda • 1 - G` has derivative `-R^2` whenever the shift is a unit. -/
theorem ringInverse_smul_one_sub_hasDerivAt
    {R : Type*}
    [NormedRing R]
    [HasSummableGeomSeries R]
    [NormedAlgebra ℝ R]
    (G : R)
    (lambda : ℝ)
    (hunit : IsUnit (lambda • (1 : R) - G)) :
    HasDerivAt
      (fun mu : ℝ => Ring.inverse (mu • (1 : R) - G))
      (-(Ring.inverse (lambda • (1 : R) - G) *
        Ring.inverse (lambda • (1 : R) - G)))
      lambda := by
  have hshift :
      HasDerivAt (fun mu : ℝ => mu • (1 : R) - G) (1 : R) lambda := by
    simpa using ((hasDerivAt_id lambda).smul_const (1 : R)).sub_const G
  have hcomp :=
    (hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit).comp_hasDerivAt lambda hshift
  have hinverse :
      Ring.inverse (lambda • (1 : R) - G) = ↑(hunit.unit⁻¹) := by
    simpa only [hunit.unit_spec] using Ring.inverse_unit hunit.unit
  simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, hinverse] using hcomp

local instance osBoundaryExcitationCompletedGeneratorRightResolventSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedGeneratorRightResolventSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedGeneratorRightResolventSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedGeneratorRightResolventSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedGeneratorRightResolventPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Positivity of the completed one-step transfer gives the sharp quadratic
upper bound `G ≤ I` for the completed discrete generator `G = I - T₁`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_le_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta u)
        u ≤ ‖u‖ ^ 2 := by
  have hT :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_inner_nonneg
      H N hN beta hbeta 1 u
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
  change inner ℝ
    (u - periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1 u) u ≤ ‖u‖ ^ 2
  rw [inner_sub_left, real_inner_self_eq_norm_sq]
  linarith

/-- The positive right spectral shift `lambda I - G`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  lambda •
      (1 :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta →L[ℝ]
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
            H N hN beta hbeta) -
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
      H N hN beta hbeta

/-- Above the exact upper generator spectral endpoint `1`, the right shift is
coercive with constant `lambda - 1`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_inner_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    (lambda - 1) * ‖u‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
          H N hN beta hbeta lambda u)
        u := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
  exact
    realContinuousLinearMap_smul_one_sub_inner_lower_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      1 lambda
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_le_norm_sq
        H N hN beta hbeta)
      u

/-- The right-shift coercivity constant is positive exactly above `1`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGap_pos
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    0 < lambda - 1 :=
  sub_pos.mpr hlambda

/-- Every right shift of the completed generator is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
        H N hN beta hbeta lambda) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
  exact
    realContinuousLinearMap_smul_one_sub_isSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta)
      lambda

/-- Every real scalar strictly above `1` belongs to the completed generator
real resolvent set. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_one_lt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    lambda ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta) := by
  by_contra hres
  have hspectrum :
      lambda ∈ spectrum ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta) := by
    change lambda ∉ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
    exact hres
  have hbounds :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_spectrum_subset_gap_to_one
      H N hN beta hbeta hspectrum
  exact (not_lt_of_ge hbounds.2) hlambda

/-- Above `1`, the positive right shift `lambda I - G` is a unit. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    IsUnit
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
        H N hN beta hbeta lambda) := by
  have hres :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_one_lt
      H N hN beta hbeta lambda hlambda
  rw [spectrum.mem_resolventSet_iff] at hres
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator,
    Algebra.algebraMap_eq_smul_one] using hres

/-- Canonical unit carried by the positive right shift. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGeneratorUnit
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)ˣ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
    H N hN beta hbeta lambda hlambda).unit

/-- The positive above-one completed right Green resolvent `(lambda I-G)⁻¹`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  ↑((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGeneratorUnit
    H N hN beta hbeta lambda hlambda)⁻¹)

/-- The positive right shift followed by its Green resolvent is the identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_mul_green
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
          H N hN beta hbeta lambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda = 1 := by
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
      H N hN beta hbeta lambda hlambda
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
          H N hN beta hbeta lambda * ↑(hG.unit⁻¹) = 1
  simpa only [hG.unit_spec] using hG.unit.mul_inv

/-- The right Green resolvent followed by the positive shift is the identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreen_mul_generator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
          H N hN beta hbeta lambda = 1 := by
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
      H N hN beta hbeta lambda hlambda
  change
    ↑(hG.unit⁻¹) *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
          H N hN beta hbeta lambda = 1
  simpa only [hG.unit_spec] using hG.unit.inv_mul

/-- Sharp operator-norm control by the distance to the upper spectral endpoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda‖ ≤ (lambda - 1)⁻¹ := by
  exact
    realContinuousLinearMap_rightInverse_norm_le_inv_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (lambda - 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGap_pos
        lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_inner_lower_bound
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)

/-- The above-one right Green resolvent is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda) := by
  apply continuousLinearMap_isSelfAdjoint_of_inner_symm
  have hShift :
      ∀ x y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta,
        inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
              H N hN beta hbeta lambda x) y =
          inner ℝ x
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
              H N hN beta hbeta lambda y) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta lambda)
  exact
    realContinuousLinearMap_rightInverse_inner_symm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      hShift
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)

/-- The right Green quadratic form is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda u)
      u := by
  exact
    realContinuousLinearMap_rightInverse_inner_nonneg_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (lambda - 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGap_pos
        lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_inner_lower_bound
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)
      u

/-- Matching quadratic upper bound for the right Green resolvent. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda u)
        u ≤
      (lambda - 1)⁻¹ * ‖u‖ ^ 2 := by
  exact
    realContinuousLinearMap_rightInverse_inner_le_inv_mul_norm_sq_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (lambda - 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGap_pos
        lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_inner_lower_bound
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)
      u

/-- Proof-independent total right-resolvent family. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  Ring.inverse
    (lambda •
        (1 :
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta →L[ℝ]
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta) -
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)

/-- Above one, the proof-independent right ring inverse equals the positive
right Green operator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda := by
  have hunit :
      IsUnit
        (lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta) -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta) := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
        H N hN beta hbeta lambda hlambda
  have hright :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda = 1 := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily] using
      mul_ringInverse_eq_one_of_isUnit
        (lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta) -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta)
        hunit
  exact
    (left_inv_eq_right_inv
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreen_mul_generator
        H N hN beta hbeta lambda hlambda)
      hright).symm

/-- The total right-resolvent family is operator-norm differentiable on the
open half-line `(1,∞)`, with derivative `-S^2`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    HasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
        H N hN beta hbeta)
      (-(periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda))
      lambda := by
  have hunit :
      IsUnit
        (lambda •
            (1 :
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta →L[ℝ]
                periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta) -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta) := by
    simpa only [
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator] using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator_isUnit_of_one_lt
        H N hN beta hbeta lambda hlambda
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily] using
    ringInverse_smul_one_sub_hasDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      lambda hunit

/-- Fixed-vector right-resolvent quadratic matrix elements have a nonpositive
first derivative above one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_hasDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    HasDerivAt
      (fun mu : ℝ =>
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta mu u)
          u)
      (- inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda) u)
        u)
      lambda := by
  have hquad :=
    HasDerivAt.quadraticEvaluation
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
        H N hN beta hbeta lambda hlambda)
      u
  simpa only [ContinuousLinearMap.neg_apply, inner_neg_left] using hquad

/-- The derivative value of every fixed-vector right-resolvent quadratic form
is nonpositive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventQuadratic_derivative_nonpos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda : 1 < lambda)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    - inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda *
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
            H N hN beta hbeta lambda) u)
        u ≤ 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_eq_green
    H N hN beta hbeta lambda hlambda]
  have hpow :
      0 ≤ inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
            H N hN beta hbeta lambda hlambda) ^ 2) u) u :=
    realContinuousLinearMap_pow_inner_nonneg_of_selfAdjoint_of_inner_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_isSelfAdjoint
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_nonneg
        H N hN beta hbeta lambda hlambda)
      2 u
  simpa [pow_two] using neg_nonpos.mpr hpow

/-- Audit-visible package for the completed positive right-resolvent calculus. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  generatorUpperQuadraticBound :
    ∀ u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta,
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta u)
          u ≤ ‖u‖ ^ 2
  aboveOneResolvent :
    ∀ lambda, 1 < lambda →
      lambda ∈ resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta)
  rightResolventPositive :
    ∀ lambda, ∀ hlambda : 1 < lambda, ∀ u,
      0 ≤ inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda u)
        u
  rightResolventNormBound :
    ∀ lambda, ∀ hlambda : 1 < lambda,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda‖ ≤ (lambda - 1)⁻¹
  rightResolventDerivative :
    ∀ lambda, 1 < lambda →
      HasDerivAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
          H N hN beta hbeta)
        (-(periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda *
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily
              H N hN beta hbeta lambda))
        lambda

/-- Construct the completed positive right-resolvent package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedGeneratorRightResolventPackage
      H N hN beta hbeta :=
  { generatorUpperQuadraticBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_le_norm_sq
        H N hN beta hbeta
    aboveOneResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_one_lt
        H N hN beta hbeta
    rightResolventPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_inner_nonneg
        H N hN beta hbeta
    rightResolventNormBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta
    rightResolventDerivative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightResolventFamily_hasDerivAt
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
