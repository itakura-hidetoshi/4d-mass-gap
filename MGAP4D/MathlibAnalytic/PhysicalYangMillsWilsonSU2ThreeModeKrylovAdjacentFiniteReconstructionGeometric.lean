import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstruction
import Mathlib.Tactic

/-!
# Geometric receiver for the finite SU(2) reconstruction residuals

PR #5119 reduces the remaining non-scalar H1-C3 geometry to three explicit
vector-wise finite reconstruction residuals:

1. physical transfer/reconstruction commutation;
2. coarse physical-carrier leakage;
3. reconstruction-range defect.

Together with the explicit weighted beta majorant from #5115, these four
nonnegative scalar sequences are sufficient for all fixed-time strong limits.

This file packages the common useful sufficient condition: each sequence is
bounded by a geometric majorant C q^n with 0 <= q < 1.

The geometric constants for the three reconstruction residuals may depend on
the fixed Krylov depth r and mode k.  No uniformity in r is required for the
fixed-natural-time H1-C3 closure.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentFiniteReconstructionGeometricTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentFiniteReconstructionGeometricCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentFiniteReconstructionGeometricSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentFiniteReconstructionGeometricMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentFiniteReconstructionGeometricBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentFiniteReconstructionGeometricSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentFiniteReconstructionGeometricSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentFiniteReconstructionGeometricNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section FiniteReconstructionGeometric

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

private theorem summable_of_nonneg_le_geometric
    (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (C q : ℝ)
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1)
    (hbound : ∀ n, f n ≤ C * q ^ n) :
    Summable f := by
  have hgeom : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left C
  exact Summable.of_nonneg_of_le hf hbound hgeom

/-- Geometric decay data for all finite reconstruction residuals.

The first three geometric constants may depend on fixed Krylov depth and mode.
The beta-majorant sequence is independent of r,k and therefore has one global
geometric certificate. -/
structure PhysicalYangMillsSU2AdjacentFiniteReconstructionGeometricInput where
  physicalCommutation_geometric :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                Q R n r k ≤
              C * q ^ n
  coarsePhysicalLeakage_geometric :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
                Q R n r k ≤
              C * q ^ n
  reconstructionRange_geometric :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
                Q R n r k ≤
              C * q ^ n
  betaMajorant_geometric :
    ∃ C q : ℝ,
      0 ≤ q ∧ q < 1 ∧
        ∀ n : ℕ,
          physicalYangMillsSU2AdjacentCouplingBetaMajorant
              halfExtent beta n ≤
            C * q ^ n

namespace PhysicalYangMillsSU2AdjacentFiniteReconstructionGeometricInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentFiniteReconstructionGeometricInput
        (Q := Q) (R := R))

include G

theorem physicalCommutation_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
          Q R n r k) := by
  rcases G.physicalCommutation_geometric r k with
    ⟨C, q, hq0, hq1, hbound⟩
  exact
    summable_of_nonneg_le_geometric
      (fun n =>
        physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
          Q R n r k)
      (fun n =>
        physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual_nonneg
          Q R n r k)
      C q hq0 hq1 hbound

theorem coarsePhysicalLeakage_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
          Q R n r k) := by
  rcases G.coarsePhysicalLeakage_geometric r k with
    ⟨C, q, hq0, hq1, hbound⟩
  exact
    summable_of_nonneg_le_geometric
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
          Q R n r k)
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual_nonneg
          Q R n r k)
      C q hq0 hq1 hbound

theorem reconstructionRange_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
          Q R n r k) := by
  rcases G.reconstructionRange_geometric r k with
    ⟨C, q, hq0, hq1, hbound⟩
  exact
    summable_of_nonneg_le_geometric
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
          Q R n r k)
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_nonneg
          Q R n r k)
      C q hq0 hq1 hbound

theorem betaMajorant_summable :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant
          halfExtent beta n) := by
  rcases G.betaMajorant_geometric with
    ⟨C, q, hq0, hq1, hbound⟩
  exact
    summable_of_nonneg_le_geometric
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant
          halfExtent beta n)
      (fun n =>
        physicalYangMillsSU2AdjacentCouplingBetaMajorant_nonneg
          halfExtent beta n)
      C q hq0 hq1 hbound

/-- Geometric finite-reconstruction decay theorem-generates the exact #5119
summability package. -/
noncomputable def toFiniteReconstructionBetaSummableInput :
    PhysicalYangMillsSU2AdjacentFiniteReconstructionBetaSummableInput
      (Q := Q) (R := R) where
  physicalCommutation_summable := physicalCommutation_summable Q R G
  coarsePhysicalLeakage_summable := coarsePhysicalLeakage_summable Q R G
  reconstructionRange_summable := reconstructionRange_summable Q R G
  betaMajorant_summable := betaMajorant_summable Q R G

/-- Therefore geometric decay of the three finite reconstruction residuals and
the explicit beta majorant is sufficient for every fixed Krylov-orbit mismatch
to be summable. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentFiniteReconstructionBetaSummableInput.orbitMismatch_summable
      Q R (toFiniteReconstructionBetaSummableInput Q R G) r k

end PhysicalYangMillsSU2AdjacentFiniteReconstructionGeometricInput

end FiniteReconstructionGeometric

end

end MathlibAnalytic
end MGAP4D
