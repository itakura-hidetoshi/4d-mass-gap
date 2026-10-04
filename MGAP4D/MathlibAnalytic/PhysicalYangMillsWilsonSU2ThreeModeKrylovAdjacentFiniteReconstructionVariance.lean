import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstruction
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedInversePythagoras
import Mathlib.Tactic

/-!
# Projection-variance form of the finite SU(2) reconstruction defects

PR #5119 leaves two purely projective finite reconstruction defects:

* reconstruction-range defect;
* coarse physical-carrier leakage.

Both are orthogonal-projection residuals.  This file identifies their squares
with exact losses of L² norm.

For the frozen-coupling fine output `y` and the canonical finite
reconstruction `R_n`,

  rangeDefect^2
    = ||y||^2 - ||R_n y||^2.

For the physical reconstruction `R_n^phys = P_phys R_n`,

  physicalLeakage^2
    = ||R_n y||^2 - ||R_n^phys y||^2.

The two losses telescope:

  rangeDefect^2 + physicalLeakage^2
    = ||y||^2 - ||R_n^phys y||^2.

This turns the two geometry residuals into a conditional-variance / projection
norm-loss problem, which is the natural interface to finite influence and
conditional-expectation estimates.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentReconstructionVarianceTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentReconstructionVarianceCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentReconstructionVarianceSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentReconstructionVarianceMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentReconstructionVarianceBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentReconstructionVarianceSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentReconstructionVarianceSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentReconstructionVarianceNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance su2AdjacentReconstructionVariancePhysicalPairCarrierComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

section ReconstructionVariance

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

/-- Squared norm lost when the frozen-coupling fine output is reconstructed in
the coarse pair-Haar carrier. -/
noncomputable def physicalYangMillsSU2AdjacentFiniteReconstructionRangeVarianceDefect
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  ‖y‖ ^ 2 - ‖Rcoarse y‖ ^ 2

/-- The reconstruction-range residual is exactly the square root carrier of the
coarse reconstruction norm loss. -/
theorem physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_sq_eq_varianceDefect
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
        Q R n r k ^ 2 =
      physicalYangMillsSU2AdjacentFiniteReconstructionRangeVarianceDefect
        Q R n r k := by
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Jleft := physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
  let Jright := physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  unfold physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
  unfold physicalYangMillsSU2AdjacentFiniteReconstructionRangeVarianceDefect
  change
    ‖Jleft (Rcoarse y) - Jright y‖ ^ 2 =
      ‖y‖ ^ 2 - ‖Rcoarse y‖ ^ 2
  have hR :
      Rcoarse y =
        realLinearIsometryProjectedInverse Jleft (Jright y) := by
    rfl
  rw [hR]
  have h :=
    realLinearIsometry_projectedInverse_residual_norm_sq_eq
      Jleft (Jright y)
  rw [Jright.norm_map] at h
  exact h

theorem physicalYangMillsSU2AdjacentFiniteReconstructionRangeVarianceDefect_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentFiniteReconstructionRangeVarianceDefect
        Q R n r k := by
  rw [←
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_sq_eq_varianceDefect
      Q R n r k]
  exact sq_nonneg _

/-- Squared norm lost by the second projection, from the reconstructed coarse
pair-Haar vector to the coarse physical pair carrier. -/
noncomputable def physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageVarianceDefect
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  let Rphys :=
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
  ‖Rcoarse y‖ ^ 2 - ‖Rphys y‖ ^ 2

/-- The coarse physical-carrier leakage residual is exactly the square root
carrier of the second projection norm loss. -/
theorem physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual_sq_eq_varianceDefect
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
        Q R n r k ^ 2 =
      physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageVarianceDefect
        Q R n r k := by
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rcoarse :=
    physicalYangMillsSU2AdjacentFiniteCoarseReconstruction Q R n
  let Rphys :=
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) 2
  unfold physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
  unfold physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageVarianceDefect
  change
    ‖Rphys y - Rcoarse y‖ ^ 2 =
      ‖Rcoarse y‖ ^ 2 - ‖Rphys y‖ ^ 2
  have h :
      Rphys y =
        realHilbertSubspaceProjection M (Rcoarse y) := by
    rfl
  rw [h]
  exact
    realHilbertSubspaceProjection_sub_norm_sq_eq M (Rcoarse y)

theorem physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageVarianceDefect_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageVarianceDefect
        Q R n r k := by
  rw [←
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual_sq_eq_varianceDefect
      Q R n r k]
  exact sq_nonneg _

/-- Total squared norm loss after the two canonical reconstruction projections:
first to the coarse pair-Haar embedding range, then to the coarse physical pair
carrier. -/
noncomputable def physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
    (n r : ℕ) (k : Fin 3) : ℝ :=
  let y :=
    physicalYangMillsSU2AdjacentFinePairFrozenCouplingStepVector
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
  let Rphys :=
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalReconstruction Q R n
  ‖y‖ ^ 2 - ‖Rphys y‖ ^ 2

/-- The two orthogonal-projection losses telescope exactly. -/
theorem
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_sq_add_coarsePhysicalLeakageResidual_sq_eq_totalVarianceDefect
    (n r : ℕ) (k : Fin 3) :
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
          Q R n r k ^ 2 +
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
          Q R n r k ^ 2 =
      physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
        Q R n r k := by
  rw [
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_sq_eq_varianceDefect
      Q R n r k,
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual_sq_eq_varianceDefect
      Q R n r k]
  unfold
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeVarianceDefect
    physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageVarianceDefect
    physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
  ring

theorem physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect_nonneg
    (n r : ℕ) (k : Fin 3) :
    0 ≤
      physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
        Q R n r k := by
  rw [←
    physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_sq_add_coarsePhysicalLeakageResidual_sq_eq_totalVarianceDefect
      Q R n r k]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

end ReconstructionVariance

end

end MathlibAnalytic
end MGAP4D
