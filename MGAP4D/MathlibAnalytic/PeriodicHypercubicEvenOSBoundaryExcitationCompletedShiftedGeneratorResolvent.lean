import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedOneStepGreenOperator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Shifting a coercive bounded real-Hilbert endomorphism by `lambda I`
subtracts exactly `lambda` from its quadratic coercivity threshold. -/
theorem realContinuousLinearMap_sub_smul_one_inner_lower_bound
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E)
    (gap lambda : ℝ)
    (hcoercive : ∀ x : E, gap * ‖x‖ ^ 2 ≤ inner ℝ (G x) x)
    (u : E) :
    (gap - lambda) * ‖u‖ ^ 2 ≤
      inner ℝ ((G - lambda • (1 : E →L[ℝ] E)) u) u := by
  have hG := hcoercive u
  change
    (gap - lambda) * ‖u‖ ^ 2 ≤
      inner ℝ (G u - lambda • u) u
  calc
    (gap - lambda) * ‖u‖ ^ 2 =
        gap * ‖u‖ ^ 2 - lambda * ‖u‖ ^ 2 := by ring
    _ ≤ inner ℝ (G u) u - lambda * ‖u‖ ^ 2 :=
      sub_le_sub_right hG _
    _ = inner ℝ (G u - lambda • u) u := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- A real scalar shift preserves self-adjointness of a bounded real-Hilbert
endomorphism. -/
theorem realContinuousLinearMap_sub_smul_one_isSelfAdjoint
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (G : E →L[ℝ] E)
    (hG : IsSelfAdjoint G)
    (lambda : ℝ) :
    IsSelfAdjoint (G - lambda • (1 : E →L[ℝ] E)) := by
  apply continuousLinearMap_isSelfAdjoint_of_inner_symm
  intro x y
  have hSymm : G.toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hG
  change
    inner ℝ (G x - lambda • x) y =
      inner ℝ x (G y - lambda • y)
  rw [inner_sub_left, inner_sub_right, hSymm x y,
    real_inner_smul_left, real_inner_smul_right]

local instance osBoundaryExcitationCompletedShiftedGeneratorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedShiftedGeneratorSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedShiftedGeneratorSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedShiftedGeneratorSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedShiftedGeneratorSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedShiftedGeneratorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedShiftedGeneratorSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedShiftedGeneratorPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The completed one-step generator shifted by a real spectral parameter.
It is written in the transfer-resolvent normal form `(1-lambda)I - T₁`, which
is exactly `G - lambda I`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  algebraMap ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
      (1 - lambda) -
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1

/-- The transfer-resolvent normal form is exactly the ordinary shifted
discrete generator `G - lambda I`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_eq_generator_sub_smul_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
        H N hN beta hbeta lambda =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
          H N hN beta hbeta -
        lambda •
          (1 :
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta →L[ℝ]
              periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
  rw [map_sub, map_one, Algebra.algebraMap_eq_smul_one]
  module

/-- The shifted generator inherits the sharp shifted coercive lower bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_inner_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda) * ‖u‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda u)
        u := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_eq_generator_sub_smul_one]
  exact
    realContinuousLinearMap_sub_smul_one_inner_lower_bound
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
        H N hN beta hbeta)
      lambda
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_inner_lower_bound
        H N hN beta hbeta)
      u

/-- Below the finite-volume generator gap, the shifted coercivity constant is
strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGap_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda :=
  sub_pos.mpr hlambda

/-- Every below-gap shifted completed generator is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
        H N hN beta hbeta lambda) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_eq_generator_sub_smul_one]
  exact
    realContinuousLinearMap_sub_smul_one_isSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta)
      lambda

/-- For every real `lambda` strictly below the finite-volume generator gap,
`(1-lambda)I - T₁ = G-lambda I` is invertible. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    IsUnit
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
        H N hN beta hbeta lambda) := by
  have hradlt :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius
          H N hN beta hbeta 1 < 1 - lambda := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap at hlambda
    linarith
  have hpos : 0 < 1 - lambda :=
    lt_trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedTransferDecayRadius_pos
        H N hN beta hbeta 1)
      hradlt
  have hres :
      (1 - lambda) ∈ resolventSet ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1) := by
    apply
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_mem_resolventSet_of_decayRadius_lt_abs
        H N hN beta hbeta 1 (by norm_num) (1 - lambda)
    simpa [abs_of_pos hpos] using hradlt
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
  exact spectrum.mem_resolventSet_iff.mp hres

/-- Equivalently, every real `lambda` below the explicit finite-volume gap is
in the real resolvent set of the completed one-step discrete generator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_lt_gap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    lambda ∈ resolventSet ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
        H N hN beta hbeta) := by
  rw [spectrum.mem_resolventSet_iff]
  have hshift :
      IsUnit
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
      H N hN beta hbeta lambda hlambda
  have hEq :
      algebraMap ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta →L[ℝ]
            periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta)
          lambda -
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta =
        -periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_eq_generator_sub_smul_one]
    rw [Algebra.algebraMap_eq_smul_one]
    module
  rw [hEq]
  exact IsUnit.neg_iff.mpr hshift

/-- The canonical unit of a below-gap shifted completed generator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGeneratorUnit
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)ˣ :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
    H N hN beta hbeta lambda hlambda).unit

/-- The positive below-gap shifted Green operator `(G-lambda I)⁻¹`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  ↑((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGeneratorUnit
    H N hN beta hbeta lambda hlambda)⁻¹)

/-- The shifted generator followed by its below-gap Green operator is the
identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_mul_green
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda = 1 := by
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
      H N hN beta hbeta lambda hlambda
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda * ↑(hG.unit⁻¹) = 1
  simpa only [hG.unit_spec] using hG.unit.mul_inv

/-- The below-gap Green operator followed by the shifted generator is also the
identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreen_mul_generator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda = 1 := by
  let hG :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isUnit_of_lt_gap
      H N hN beta hbeta lambda hlambda
  change
    ↑(hG.unit⁻¹) *
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda = 1
  simpa only [hG.unit_spec] using hG.unit.inv_mul

/-- The below-gap shifted Green operator satisfies the sharp coercive inverse
bound `‖(G-lambda I)⁻¹‖ ≤ (gap-lambda)⁻¹`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)⁻¹ := by
  exact
    realContinuousLinearMap_rightInverse_norm_le_inv_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGap_pos
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_inner_lower_bound
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)

/-- The below-gap shifted Green operator is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda) := by
  apply continuousLinearMap_isSelfAdjoint_of_inner_symm
  have hShift :
      ∀ x y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta,
        inner ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
              H N hN beta hbeta lambda x) y =
          inner ℝ x
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
              H N hN beta hbeta lambda y) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta lambda)
  exact
    realContinuousLinearMap_rightInverse_inner_symm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      hShift
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)

/-- The below-gap shifted Green quadratic form is nonnegative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda u)
      u := by
  exact
    realContinuousLinearMap_rightInverse_inner_nonneg_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGap_pos
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_inner_lower_bound
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)
      u

/-- The below-gap shifted Green quadratic form is bounded above by the inverse
spectral distance to the explicit finite-volume gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_inner_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      lambda <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda u)
        u ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)⁻¹ * ‖u‖ ^ 2 := by
  exact
    realContinuousLinearMap_rightInverse_inner_le_inv_mul_norm_sq_of_coercive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
          H N hN beta hbeta - lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGap_pos
        H N hN beta hbeta lambda hlambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_inner_lower_bound
        H N hN beta hbeta lambda)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_mul_green
        H N hN beta hbeta lambda hlambda)
      u

/-- Audit-visible below-gap real-resolvent package for the completed one-step
discrete excitation generator. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedShiftedGeneratorResolventPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  belowGapResolvent :
    ∀ lambda : ℝ,
      lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta →
        lambda ∈ resolventSet ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator
            H N hN beta hbeta)
  shiftedCoercivity :
    ∀ (lambda : ℝ)
      (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta),
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda) * ‖u‖ ^ 2 ≤
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
            H N hN beta hbeta lambda u)
          u
  shiftedSelfAdjoint :
    ∀ lambda : ℝ,
      IsSelfAdjoint
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator
          H N hN beta hbeta lambda)
  shiftedGreenNormBound :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)⁻¹
  shiftedGreenSelfAdjoint :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta),
      IsSelfAdjoint
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda)
  shiftedGreenQuadraticNonnegative :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta),
      0 ≤ inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
          H N hN beta hbeta lambda hlambda u)
        u
  shiftedGreenQuadraticUpperBound :
    ∀ (lambda : ℝ)
      (hlambda :
        lambda <
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta)
      (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta),
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator
            H N hN beta hbeta lambda hlambda u)
          u ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGeneratorGap
            H N hN beta hbeta - lambda)⁻¹ * ‖u‖ ^ 2

/-- Construct the completed below-gap shifted-generator resolvent package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedShiftedGeneratorResolventPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedShiftedGeneratorResolventPackage
      H N hN beta hbeta :=
  { belowGapResolvent :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorOneStepGenerator_mem_resolventSet_of_lt_gap
        H N hN beta hbeta
    shiftedCoercivity :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_inner_lower_bound
        H N hN beta hbeta
    shiftedSelfAdjoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGenerator_isSelfAdjoint
        H N hN beta hbeta
    shiftedGreenNormBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_norm_le
        H N hN beta hbeta
    shiftedGreenSelfAdjoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_isSelfAdjoint
        H N hN beta hbeta
    shiftedGreenQuadraticNonnegative :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_inner_nonneg
        H N hN beta hbeta
    shiftedGreenQuadraticUpperBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorShiftedOneStepGreenOperator_inner_le
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D