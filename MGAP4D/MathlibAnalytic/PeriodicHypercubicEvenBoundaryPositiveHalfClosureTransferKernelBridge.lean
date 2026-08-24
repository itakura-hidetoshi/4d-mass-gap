import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfClosureCylinderActionIdentification
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 2000000

/-- Replacing the time coordinate of a primary-slice vertex by zero returns the
same four-dimensional vertex. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceVertexAtTime_zero_eq
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenSpatialSliceVertexAtTime H
        (0 : ZMod (PeriodicHypercubicEvenSideLength H)) v = v.1 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenSpatialSliceVertexAtTime, v.2]
  · simp [periodicHypercubicEvenSpatialSliceVertexAtTime, hi]

/-- Replacing the time coordinate of a primary-slice vertex by the antipodal
half-period is exactly the canonical half-period time translation. -/
@[simp] theorem periodicHypercubicEvenSpatialSliceVertexAtTime_halfPeriod_eq
    (H : ℕ)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenSpatialSliceVertexAtTime H
        (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) v =
      periodicHypercubicEvenHalfPeriodTimeShift H v.1 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicEvenHalfPeriodTimeShift, v.2]
  · simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicEvenHalfPeriodTimeShift, hi]

/-- The spatial path extracted from the positive-half representative assembled
from `(b,x)` is exactly the spatial component of the canonical positive-closure
to transfer-coordinate equivalence. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedAssemble_positiveHalfSpatialPathRestriction_eq_transfer
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)) =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 := by
  funext j e
  by_cases hzero : j.1 = 0
  · have hj : j = 0 := Fin.ext hzero
    subst j
    change
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)
          (periodicHypercubicEvenSpatialSliceLinkAtTime H 0 e) = _
    have hedge :
        periodicHypercubicEvenSpatialSliceLinkAtTime H 0 e =
          (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e).1 := by
      unfold periodicHypercubicEvenSpatialSliceLinkAtTime
      rw [periodicHypercubicEvenSpatialSliceVertexAtTime_zero_eq]
      rfl
    rw [hedge]
    rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
      b x (fun _ => 1) (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)]
    simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv,
      periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
      periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
      periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
      periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
      periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath,
      periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex,
      periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
      periodicHypercubicEvenSpatialSliceSumToFixedEdge,
      periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge]
  · by_cases hlast : j.1 = H + 1
    · have hj : j = ⟨H + 1, by omega⟩ := Fin.ext hlast
      rw [hj]
      change
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1)
            (periodicHypercubicEvenSpatialSliceLinkAtTime H
              (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) e) = _
      have hedge :
          periodicHypercubicEvenSpatialSliceLinkAtTime H
              (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) e =
            (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
              (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)).1 := by
        unfold periodicHypercubicEvenSpatialSliceLinkAtTime
        rw [periodicHypercubicEvenSpatialSliceVertexAtTime_halfPeriod_eq]
        rfl
      rw [hedge]
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
        b x (fun _ => 1)
        (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
          (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e))]
      simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv,
        periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
        periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
        periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
        periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
        periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath,
        periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex,
        periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
        periodicHypercubicEvenSpatialSliceSumToFixedEdge,
        periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge,
        periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv,
        periodicHypercubicEvenPrimaryAntipodalSpatialSliceVertexEquiv,
        periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex]
    · have hjpos : 1 ≤ j.1 := by omega
      have hjle : j.1 ≤ H := by
        have hjlt := j.2
        omega
      let k : Fin H := ⟨j.1 - 1, by omega⟩
      have hk : k.1 + 1 = j.1 := by
        dsimp [k]
        omega
      have hj : j = ⟨k.1 + 1, by omega⟩ := by
        apply Fin.ext
        exact hk.symm
      rw [hj]
      change
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1)
            (periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H (k, e)) = _
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
        b x (fun _ => 1)
        (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H (Sum.inl (k, e)))]
      simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv,
        periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
        periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
        periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
        periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
        periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath,
        periodicHypercubicEvenPositiveHalfPathToBoundaryInteriorSpatialIndex,
        periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex,
        periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge,
        k]

/-- The temporal-link field extracted from the same assembled representative is
exactly the temporal component of the canonical positive-closure transfer
coordinates. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryFiberedAssemble_positiveHalfTemporalFieldRestriction_eq_transfer
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)) =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).2 := by
  funext i v
  change
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
        b x (fun _ => 1)
        (periodicHypercubicEvenPositiveHalfTemporalEdge H (i, v)) = _
  rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
    b x (fun _ => 1)
    (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H (Sum.inr (i, v)))]
  simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
    periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex,
    periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge]

/-- Specializing the geometric action bridge to the positive-half representative
assembled from boundary/open-half data identifies the OS closure action with the
unfixed cylinder action on the canonical transfer coordinates. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction_eq_unfixedPathAction_transfer
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction H N b x =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N (b, x)).1
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H N (b, x)).2 := by
  let A :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      b x (fun _ => 1)
  have haction :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSectorAction_eq_unfixedPathAction
      H N A
  have hspatial :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedAssemble_positiveHalfSpatialPathRestriction_eq_transfer
      H N b x
  have htemporal :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedAssemble_positiveHalfTemporalFieldRestriction_eq_transfer
      H N b x
  simpa [periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction, A,
    hspatial, htemporal] using haction

/-- The unfixed finite-cylinder path kernel is the Boltzmann exponential of the
complete unfixed path action. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_boltzmann
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta path U =
      Real.exp
        (-beta *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
            H N path U) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
  unfold periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabKernel
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- Pointwise normalized OS positive-half Boltzmann amplitude equals the same
partition square-root normalization times the unfixed transfer-cylinder kernel
on the canonical positive-half coordinates. -/
theorem periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude_eq_normalizedUnfixedPathKernel
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
        H N hN beta hbeta b x =
      periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N (b, x)).1
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N (b, x)).2 := by
  unfold periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
  rw [periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction_eq_unfixedPathAction_transfer
    H N b x]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_boltzmann]

/-- Terminal pointwise bridge for this unit: the existing completed positive OS
Gram feature is exactly the partition-normalized unfixed transfer-cylinder
kernel in the canonical positive-half transfer coordinates. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedUnfixedPathKernel
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x =
      periodicHypercubicEvenBoundaryPositiveHalfPartitionSqrtNormalization
          H N hN beta hbeta *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N (b, x)).1
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N (b, x)).2 := by
  calc
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta b x =
      periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude
        H N hN beta hbeta b x :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_normalizedClosureBoltzmann
        H N hN beta hbeta b x
    _ = _ :=
      periodicHypercubicEvenBoundaryNormalizedPositiveHalfClosureBoltzmannAmplitude_eq_normalizedUnfixedPathKernel
        H N hN beta hbeta b x

end

end MathlibAnalytic
end MGAP4D
