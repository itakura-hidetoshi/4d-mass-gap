import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedTransferPositivity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- An upper quadratic bound becomes coercivity for the right shift `lambda I - G`. -/
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

/-- A right scalar shift of a self-adjoint bounded real-Hilbert endomorphism is self-adjoint. -/
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
  calc
    inner ℝ (lambda • x - G x) y =
        lambda * inner ℝ x y - inner ℝ (G x) y := by
      rw [inner_sub_left, real_inner_smul_left]
    _ = lambda * inner ℝ x y - inner ℝ x (G y) := by
      have hxy : inner ℝ (G x) y = inner ℝ x (G y) := by
        simpa using hSymm x y
      rw [hxy]
    _ = inner ℝ x (lambda • y - G y) := by
      rw [inner_sub_right, real_inner_smul_right]

local instance osBoundaryExcitationCompletedGeneratorRightResolventCoreSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedGeneratorRightResolventCoreSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventCoreSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedGeneratorRightResolventCoreSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventCoreSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedGeneratorRightResolventCoreSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedGeneratorRightResolventCoreSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedGeneratorRightResolventCorePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Transfer positivity gives the sharp quadratic upper bound `G ≤ I`. -/
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
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  change inner ℝ (u - T u) u ≤ ‖u‖ ^ 2
  have hsplit :
      inner ℝ (u - T u) u = inner ℝ u u - inner ℝ (T u) u := by
    simpa only [inner_sub_left]
  rw [hsplit, real_inner_self_eq_norm_sq]
  change 0 ≤ inner ℝ (T u) u at hT
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

/-- The right shift is coercive with lower bound `(lambda - 1)‖u‖²`. -/
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
  have hupper :
      ∀ x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta,
        inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
              H N hN beta hbeta x)
            x ≤ (1 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    simpa using
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_le_norm_sq
        H N hN beta hbeta x
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGenerator
  exact
    realContinuousLinearMap_smul_one_sub_inner_lower_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      1 lambda hupper u

/-- Above one the right-shift coercivity parameter is positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorRightShiftedOneStepGap_pos
    (lambda : ℝ)
    (hlambda : 1 < lambda) :
    0 < lambda - 1 :=
  sub_pos.mpr hlambda

/-- Every right shift is self-adjoint. -/
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

/-- Every `lambda > 1` is in the real resolvent set of the completed generator. -/
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

/-- Above one the right shift `lambda I - G` is a unit. -/
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

/-- The positive right Green resolvent `(lambda I-G)⁻¹`. -/
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

/-- The right shift followed by its Green resolvent is the identity. -/
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

/-- The Green resolvent followed by the right shift is the identity. -/
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

/-- Sharp norm control by the distance to the upper spectral endpoint. -/
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

/-- The right Green resolvent is self-adjoint. -/
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

end

end MathlibAnalytic
end MGAP4D
