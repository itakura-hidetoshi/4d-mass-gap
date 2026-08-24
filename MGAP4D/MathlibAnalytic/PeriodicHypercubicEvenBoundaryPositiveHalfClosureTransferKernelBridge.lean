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
    have hv := v.2
    unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hv
    simpa [periodicHypercubicEvenSpatialSliceVertexAtTime] using hv.symm
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
    have hv := v.2
    unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hv
    simpa [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicEvenHalfPeriodTimeShift] using hv
  · simp [periodicHypercubicEvenSpatialSliceVertexAtTime,
      periodicHypercubicEvenHalfPeriodTimeShift, hi]

private theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 0 e =
      b ((periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).symm (Sum.inl e)) := by
  let sourceIndex :=
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge
  let targetIndex := PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H
  let A : sourceIndex → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : sourceIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (b, x)
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : targetIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)
      (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H) A
      (Sum.inl ((periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).symm (Sum.inl e)))
  simpa [sourceIndex, targetIndex, A,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath] using h

private theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 ⟨H + 1, by
          simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
          omega⟩ e =
      b ((periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).symm (Sum.inr e)) := by
  let sourceIndex :=
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge
  let targetIndex := PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H
  let A : sourceIndex → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : sourceIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (b, x)
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : targetIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)
      (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H) A
      (Sum.inl ((periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).symm (Sum.inr e)))
  simpa [sourceIndex, targetIndex, A,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath] using h

private theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_interior_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (k : Fin H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 ⟨k.1 + 1, by
          simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
          omega⟩ e =
      x ((periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).symm
        (Sum.inl (k, e))) := by
  let sourceIndex :=
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge
  let targetIndex := PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H
  let A : sourceIndex → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : sourceIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (b, x)
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : targetIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)
      (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H) A
      (Sum.inr ((periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).symm
        (Sum.inl (k, e))))
  simpa [sourceIndex, targetIndex, A,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath] using h

private theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_temporal_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).2 i v =
      x ((periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).symm
        (Sum.inr (i, v))) := by
  let sourceIndex :=
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge
  let targetIndex := PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H
  let A : sourceIndex → Matrix.specialUnitaryGroup (Fin N) ℂ :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : sourceIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (b, x)
  have h :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : targetIndex => Matrix.specialUnitaryGroup (Fin N) ℂ)
      (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H) A
      (Sum.inr ((periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).symm
        (Sum.inr (i, v))))
  simpa [sourceIndex, targetIndex, A,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv,
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv] using h

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
    let ef := (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).symm (Sum.inl e)
    have hedge :
        periodicHypercubicEvenSpatialSliceLinkAtTime H 0 e = ef.1 := by
      dsimp [ef, periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
        periodicHypercubicEvenSpatialSliceSumToFixedEdge,
        periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge]
      unfold periodicHypercubicEvenSpatialSliceLinkAtTime
      rw [periodicHypercubicEvenSpatialSliceVertexAtTime_zero_eq]
    change
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)
          (periodicHypercubicEvenSpatialSliceLinkAtTime H 0 e) = _
    rw [hedge]
    rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
      b x (fun _ => 1) ef]
    exact (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_apply
      H N b x e).symm
  · by_cases hlast : j.1 = H + 1
    · have hj : j = ⟨H + 1, by
          simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
          omega⟩ := Fin.ext hlast
      rw [hj]
      let ef := (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).symm (Sum.inr e)
      have hedge :
          periodicHypercubicEvenSpatialSliceLinkAtTime H
              (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) e = ef.1 := by
        dsimp [ef, periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
          periodicHypercubicEvenSpatialSliceSumToFixedEdge,
          periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge,
          periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv,
          periodicHypercubicEvenPrimaryAntipodalSpatialSliceVertexEquiv,
          periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex]
        unfold periodicHypercubicEvenSpatialSliceLinkAtTime
        rw [periodicHypercubicEvenSpatialSliceVertexAtTime_halfPeriod_eq]
      change
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1)
            (periodicHypercubicEvenSpatialSliceLinkAtTime H
              (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))) e) = _
      rw [hedge]
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
        b x (fun _ => 1) ef]
      exact (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_apply
        H N b x e).symm
    · have hjpos : 1 ≤ j.1 := by omega
      have hjle : j.1 ≤ H := by
        have hjlt := j.2
        simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount] at hjlt
        omega
      let k : Fin H := ⟨j.1 - 1, by omega⟩
      have hk : k.1 + 1 = j.1 := by
        dsimp [k]
        omega
      have hj : j = ⟨k.1 + 1, by
          simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
          omega⟩ := by
        apply Fin.ext
        exact hk.symm
      rw [hj]
      let ep := (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).symm
        (Sum.inl (k, e))
      have hedge :
          periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H (k, e) = ep.1 := by
        dsimp [ep]
        simp [periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex,
          periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge]
      change
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1)
            (periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H (k, e)) = _
      rw [hedge]
      rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
        b x (fun _ => 1) ep]
      exact (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_interior_apply
        H N b x k e).symm

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
  let ep := (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).symm
    (Sum.inr (i, v))
  have hedge :
      periodicHypercubicEvenPositiveHalfTemporalEdge H (i, v) = ep.1 := by
    dsimp [ep]
    simp [periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex,
      periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge]
  change
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
        b x (fun _ => 1)
        (periodicHypercubicEvenPositiveHalfTemporalEdge H (i, v)) = _
  rw [hedge]
  rw [(periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
    b x (fun _ => 1) ep]
  exact (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_temporal_apply
    H N b x i v).symm

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