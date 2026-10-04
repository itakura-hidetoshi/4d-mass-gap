import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionGeometric
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFiniteReconstructionVariance
import MGAP4D.MathlibAnalytic.RealVarianceGeometricSqrtReceiver
import Mathlib.Tactic

/-!
# Variance-tail receiver for adjacent SU(2) finite reconstruction geometry

PR #5120 consumes geometric bounds for three finite reconstruction residuals:

1. physical transfer/reconstruction commutation;
2. coarse physical-carrier leakage;
3. reconstruction-range defect.

PR #5122 identifies the squares of the last two residuals as two orthogonal
projection norm losses which telescope to one total reconstruction variance
defect.

Therefore a single growing-distance geometric tail for the total variance
defect simultaneously generates geometric bounds for both projective residuals.
The square root changes the geometric rate from rho to sqrt(rho), which remains
strictly below one.

The only remaining independently geometric non-scalar input is then the finite
physical transfer/reconstruction commutation residual.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentVarianceGeometricTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentVarianceGeometricCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentVarianceGeometricSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentVarianceGeometricMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentVarianceGeometricBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentVarianceGeometricSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentVarianceGeometricSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentVarianceGeometricNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section VarianceGeometric

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

/-- Model-facing geometric input after combining the two projection residuals
into one total reconstruction variance tail.

The distance function and constants may depend on fixed Krylov depth and mode.
No uniformity in r,k is required. -/
structure PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput where
  physicalCommutation_geometric :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ C q : ℝ,
        0 ≤ q ∧ q < 1 ∧
          ∀ n : ℕ,
            physicalYangMillsSU2AdjacentFinitePhysicalReconstructionCommutationResidual
                Q R n r k ≤
              C * q ^ n
  totalVariance_tail :
    ∀ (r : ℕ) (k : Fin 3),
      ∃ (C rho : ℝ) (distance : ℕ → ℕ),
        0 ≤ C ∧
        0 ≤ rho ∧
        rho < 1 ∧
        (∀ n, n ≤ distance n) ∧
        ∀ n,
          physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
              Q R n r k ≤
            C * (rho ^ distance n / (1 - rho))
  betaMajorant_geometric :
    ∃ C q : ℝ,
      0 ≤ q ∧ q < 1 ∧
        ∀ n : ℕ,
          physicalYangMillsSU2AdjacentCouplingBetaMajorant
              halfExtent beta n ≤
            C * q ^ n

namespace PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput

variable
    (G :
      PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput
        (Q := Q) (R := R))

include G

/-- The reconstruction-range residual inherits scale-geometric decay from the
single total reconstruction variance tail. -/
theorem reconstructionRange_geometric
    (r : ℕ) (k : Fin 3) :
    ∃ C q : ℝ,
      0 ≤ q ∧ q < 1 ∧
        ∀ n : ℕ,
          physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
              Q R n r k ≤
            C * q ^ n := by
  rcases G.totalVariance_tail r k with
    ⟨C, rho, distance, hC, hrho0, hrho1, hDistance, hTail⟩
  refine
    ⟨Real.sqrt (C / (1 - rho)), Real.sqrt rho,
      Real.sqrt_nonneg rho,
      real_sqrt_lt_one_of_nonneg_of_lt_one rho hrho0 hrho1,
      ?_⟩
  exact
    real_le_sqrt_scale_geometric_of_sq_le_geometric_tail_of_index_le_distance
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
          Q R n r k)
      distance C rho hC hrho0 hrho1 hDistance
      (fun n => by
        have hsqToTotal :
            physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual
                Q R n r k ^ 2 ≤
              physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
                Q R n r k := by
          rw [←
            physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_sq_add_coarsePhysicalLeakageResidual_sq_eq_totalVarianceDefect
              Q R n r k]
          exact le_add_of_nonneg_right (sq_nonneg _)
        exact hsqToTotal.trans (hTail n))

/-- The coarse physical-carrier leakage residual inherits the same
scale-geometric envelope from the same total variance tail. -/
theorem coarsePhysicalLeakage_geometric
    (r : ℕ) (k : Fin 3) :
    ∃ C q : ℝ,
      0 ≤ q ∧ q < 1 ∧
        ∀ n : ℕ,
          physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
              Q R n r k ≤
            C * q ^ n := by
  rcases G.totalVariance_tail r k with
    ⟨C, rho, distance, hC, hrho0, hrho1, hDistance, hTail⟩
  refine
    ⟨Real.sqrt (C / (1 - rho)), Real.sqrt rho,
      Real.sqrt_nonneg rho,
      real_sqrt_lt_one_of_nonneg_of_lt_one rho hrho0 hrho1,
      ?_⟩
  exact
    real_le_sqrt_scale_geometric_of_sq_le_geometric_tail_of_index_le_distance
      (fun n =>
        physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
          Q R n r k)
      distance C rho hC hrho0 hrho1 hDistance
      (fun n => by
        have hsqToTotal :
            physicalYangMillsSU2AdjacentFiniteCoarsePhysicalLeakageResidual
                Q R n r k ^ 2 ≤
              physicalYangMillsSU2AdjacentFiniteTotalReconstructionVarianceDefect
                Q R n r k := by
          rw [←
            physicalYangMillsSU2AdjacentFiniteReconstructionRangeResidual_sq_add_coarsePhysicalLeakageResidual_sq_eq_totalVarianceDefect
              Q R n r k]
          exact le_add_of_nonneg_left (sq_nonneg _)
        exact hsqToTotal.trans (hTail n))

/-- A single total-variance tail supplies both projective geometric fields of
the #5120 finite reconstruction receiver. -/
noncomputable def toFiniteReconstructionGeometricInput :
    PhysicalYangMillsSU2AdjacentFiniteReconstructionGeometricInput
      (Q := Q) (R := R) where
  physicalCommutation_geometric := G.physicalCommutation_geometric
  coarsePhysicalLeakage_geometric := coarsePhysicalLeakage_geometric Q R G
  reconstructionRange_geometric := reconstructionRange_geometric Q R G
  betaMajorant_geometric := G.betaMajorant_geometric

/-- Hence physical commutation decay, one total reconstruction variance tail,
and the beta majorant already imply every fixed Krylov-orbit mismatch is
summable. -/
theorem orbitMismatch_summable
    (r : ℕ) (k : Fin 3) :
    Summable
      (fun n =>
        physicalYangMillsSU2AdjacentCommonTransferRightOrbitMismatch
          Q R n r k) := by
  exact
    PhysicalYangMillsSU2AdjacentFiniteReconstructionGeometricInput.orbitMismatch_summable
      Q R (toFiniteReconstructionGeometricInput Q R G) r k

end PhysicalYangMillsSU2AdjacentFiniteReconstructionVarianceGeometricInput

end VarianceGeometric

end

end MathlibAnalytic
end MGAP4D
