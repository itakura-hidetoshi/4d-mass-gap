import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionVarianceGeometric
import MGAP4D.MathlibAnalytic.RealLinearIsometrySubspaceProjectedCompressionProjection
import Mathlib.Tactic

/-!
# Common-marginal orthogonal projection form of SU(2) reconstruction variance

PR #5122 combines the reconstruction-range and coarse-physical leakage defects
into one total reconstruction variance defect

  ||y||^2 - ||R_n^phys y||^2.

The generic projection theorem identifies

  J_n^L ∘ P_phys,n ∘ (J_n^L)^{-1}_proj

with the canonical orthogonal projection onto the coarse embedded physical pair
carrier inside the adjacent common marginal.

Consequently the total reconstruction variance defect is exactly one ambient
orthogonal-projection residual squared:

  V_{n,r,k} = ||Y_{n,r,k} - P_n^phys Y_{n,r,k}||^2,

where `Y_{n,r,k}` is the fine frozen-coupling output embedded in the common
marginal.

This is the direct interface to the existing conditional-expectation projection
comparison machinery.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentCommonPhysicalProjectionTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentCommonPhysicalProjectionCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentCommonPhysicalProjectionSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentCommonPhysicalProjectionMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentCommonPhysicalProjectionBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentCommonPhysicalProjectionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentCommonPhysicalProjectionSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentCommonPhysicalProjectionNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance su2AdjacentCommonPhysicalProjectionPairCarrierComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

section CommonPhysicalProjection

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

/-- Orthogonal projection in the adjacent common marginal onto the coarse
embedded completed physical pair carrier. -/
noncomputable def physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
    (n : ℕ) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  realLinearIsometrySubspaceProjectedCompression
    (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) 2)
    (1 :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent n) 2 →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
          (halfExtent n) 2)

/-- The common-marginal physical reconstruction projection is exactly
Mathlib's star projection onto the coarse embedded physical pair subspace. -/
theorem physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection_eq_starProjection
    (n : ℕ) :
    physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection Q R n =
      ((periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent n) 2).map
        (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n).toLinearMap
      ).starProjection := by
  unfold physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
  exact
    realLinearIsometrySubspaceProjectedCompression_one_eq_starProjection_map
      (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2)

/-- Applying the common-marginal physical projection to a fine embedded vector
is exactly coarse physical reconstruction followed by the coarse embedding. -/
theorem physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection_apply_rightPairEmbedding
    (n : ℕ)
    (y :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2) :
    physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection Q R n
        (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n y) =
      physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
        (physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction
          Q R n y) := by
  unfold
    physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction
    realLinearIsometrySubspaceProjectedCompression
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

/-- The frozen-coupling fine output placed in the adjacent common marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
    (n r : ℕ) (k : Fin 3) :
    Lp ℝ 2
      (F.finiteMarginal
        (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
          (Q := Q) R n)) :=
  physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
    (physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k)

/-- The #5122 total reconstruction variance defect is exactly one
common-marginal orthogonal-projection residual squared. -/
theorem
    physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect_eq_commonPhysicalProjectionResidual_sq
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
        Q R n r k =
      ‖physicalYangMillsSU2AdjacentCommonFineFrozenStepVector Q R n r k -
        physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection Q R n
          (physicalYangMillsSU2AdjacentCommonFineFrozenStepVector
            Q R n r k)‖ ^ 2 := by
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  let Jleft := physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
  let Jright := physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) 2
  let P :=
    physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection Q R n
  let Rphys :=
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
  have hPyth :
      ‖Jright y -
          realLinearIsometrySubspaceProjectedCompression
            Jleft M
            (1 :
              PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
                  (halfExtent n) 2 →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
                  (halfExtent n) 2)
            (Jright y)‖ ^ 2 =
        ‖Jright y‖ ^ 2 -
          ‖realLinearIsometrySubspaceProjectedCompression
            Jleft M
            (1 :
              PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
                  (halfExtent n) 2 →L[ℝ]
                PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
                  (halfExtent n) 2)
            (Jright y)‖ ^ 2 :=
    realLinearIsometrySubspaceProjectedCompression_one_residual_norm_sq_eq
      Jleft M (Jright y)
  have hPapply : P (Jright y) = Jleft (Rphys y) := by
    dsimp [P, Jleft, Jright, Rphys]
    exact
      physicalYangMillsSU2AdjacentCommonLeftPhysicalRangeProjection_apply_rightPairEmbedding
        Q R n y
  change
    ‖y‖ ^ 2 - ‖Rphys y‖ ^ 2 =
      ‖Jright y - P (Jright y)‖ ^ 2
  rw [hPapply, Jright.norm_map, Jleft.norm_map]
  simpa [P, Jleft, M] using hPyth.symm

end CommonPhysicalProjection

end

end MathlibAnalytic
end MGAP4D
