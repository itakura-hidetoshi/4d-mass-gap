import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentCommonTransferPerturbation
import MGAP4D.MathlibAnalytic.RealLinearIsometrySubspaceProjectedCompressionPerturbation
import Mathlib.Tactic

/-!
# Split the adjacent SU(2) common-transfer mismatch into geometry and coupling

The #5103 strong-limit bridge leaves one model-facing quantity,

  ||A_n^L - A_n^R||,

where the left operator lives at halfExtent n, beta n and the right operator at
halfExtent (n+1), beta (n+1), after both are compressed to one common finite
marginal.

This file inserts the actual fine-volume operator at the *coarse coupling*
beta n.  The triangle inequality then separates the adjacent mismatch into

  cross-volume geometry/refinement residual at frozen beta n

plus

  same-fine-volume Wilson-coupling residual.

The second term is no larger than the operator-norm difference of the actual
normalized physical pair transfers at the same fine volume, because projected
compression is 1-Lipschitz in its operator argument.

No transfer compatibility, exact cross-volume intertwining, vacuum alignment,
or H1-D5 assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentSplitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentSplitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentSplitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentSplitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentSplitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentSplitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentSplitSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentSplitNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section AdjacentTransferMismatchSplit

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)

local instance su2AdjacentSplitPhysicalPairCarrierComplete (n : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

/-- The fine-volume common-marginal compression evaluated at an arbitrary
nonnegative Wilson coupling.  The spatial volume and the embedding are fixed
at scale n+1; only the coupling changes. -/
noncomputable def physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
    (n : ℕ) (gamma : ℝ) (hgamma : 0 ≤ gamma) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  realLinearIsometrySubspaceProjectedCompression
    (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n)
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent (n + 1)) 2)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      gamma hgamma)

/-- At the actual fine coupling, the interpolating compression is definitionally
the #5102 right common transfer. -/
@[simp] theorem physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_beta_succ
    (n : ℕ) :
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
        Q R n (beta (n + 1)) (hbeta (n + 1)) =
      physicalYangMillsSU2AdjacentCommonRightTransfer Q R n := by
  rfl

/-- Same-volume coupling changes cannot be enlarged by the common-marginal
projected compression. -/
theorem physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_norm_sub_le
    (n : ℕ)
    (gamma delta : ℝ)
    (hgamma : 0 ≤ gamma)
    (hdelta : 0 ≤ delta) :
    ‖physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n gamma hgamma -
        physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n delta hdelta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          gamma hgamma -
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          delta hdelta‖ := by
  unfold physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
  exact
    realLinearIsometrySubspaceProjectedCompression_norm_sub_le
      (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent (n + 1)) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        gamma hgamma)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        delta hdelta)

/-- Pure cross-volume/refinement residual after freezing the Wilson coupling at
the coarse value beta n.  This is the genuinely geometric part of the adjacent
operator mismatch. -/
noncomputable def physicalYangMillsSU2AdjacentCommonTransferGeometryResidual
    (n : ℕ) : ℝ :=
  ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
    physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
      Q R n (beta n) (hbeta n)‖

theorem physicalYangMillsSU2AdjacentCommonTransferGeometryResidual_nonneg
    (n : ℕ) :
    0 ≤ physicalYangMillsSU2AdjacentCommonTransferGeometryResidual Q R n :=
  norm_nonneg _

/-- Exact model-facing split: the full adjacent common-transfer mismatch is at
most the frozen-coupling cross-volume geometry residual plus the same-fine-
volume normalized-pair coupling residual. -/
theorem physicalYangMillsSU2AdjacentCommonTransferMismatch_le_geometry_add_coupling
    (n : ℕ) :
    ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
      physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ ≤
      physicalYangMillsSU2AdjacentCommonTransferGeometryResidual Q R n +
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) -
          periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta (n + 1)) (hbeta (n + 1))‖ := by
  calc
    ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ ≤
      ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
        physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n (beta n) (hbeta n)‖ +
      ‖physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
          Q R n (beta n) (hbeta n) -
        physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ := by
      rw [show
        physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransfer Q R n =
          (physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n)) +
          (physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n) -
            physicalYangMillsSU2AdjacentCommonRightTransfer Q R n) by abel]
      exact norm_add_le _ _
    _ ≤
      physicalYangMillsSU2AdjacentCommonTransferGeometryResidual Q R n +
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) -
          periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta (n + 1)) (hbeta (n + 1))‖ := by
      rw [physicalYangMillsSU2AdjacentCommonTransferGeometryResidual]
      rw [← physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_beta_succ
        Q R n]
      exact
        add_le_add_right
          (physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling_norm_sub_le
            Q R n (beta n) (beta (n + 1)) (hbeta n) (hbeta (n + 1)))
          ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n -
            physicalYangMillsSU2AdjacentCommonRightTransferAtCoupling
              Q R n (beta n) (hbeta n)‖

end AdjacentTransferMismatchSplit

end

end MathlibAnalytic
end MGAP4D
