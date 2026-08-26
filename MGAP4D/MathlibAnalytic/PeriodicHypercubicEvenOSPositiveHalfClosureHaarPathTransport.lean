import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSPositiveHalfAmplitudePathKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCoordinateTransferBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance osPositiveHalfClosureHaarPathTransportSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osPositiveHalfClosureHaarPathTransportSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osPositiveHalfClosureHaarPathTransportSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osPositiveHalfClosureHaarPathTransportSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osPositiveHalfClosureHaarPathTransportSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Evaluating the positive-closure flat reindexing at the image of a source
index reads exactly the original source coordinate.  This is the stable
`piCongrLeft` interface used below instead of unfolding the whole measurable
reindexing at every geometric sector. -/
private theorem periodicHypercubicEvenPositiveHalfClosureFlat_reindexed_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (s : (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge) :
    ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H =>
          Matrix.specialUnitaryGroup (Fin N) ℂ)).symm
      (periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ) (b, x)))
      (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H s) =
    ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ :
          (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
            (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge =>
          Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (b, x)) s := by
  simpa [periodicHypercubicEvenPositiveHalfClosureFlatMeasurableEquiv] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : PeriodicHypercubicEvenPositiveHalfClosureFlatIndex H =>
        Matrix.specialUnitaryGroup (Fin N) ℂ)
      (periodicHypercubicEvenPositiveHalfClosureIndexEquiv H)
      ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ :
          (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge ⊕
            (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge =>
          Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (b, x)) s)

private theorem periodicHypercubicEvenPositiveHalfClosureIndexEquiv_primary
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv H
        (Sum.inl (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)) =
      Sum.inl (0, e) := by
  have hfixed :
      periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H
          (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) =
        Sum.inl e := by
    simpa [periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
      periodicHypercubicEvenSpatialSliceSumToFixedEdge] using
      (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).apply_symm_apply
        (Sum.inl e)
  simp [periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath,
    hfixed]

private theorem periodicHypercubicEvenPositiveHalfClosureIndexEquiv_antipodal
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv H
        (Sum.inl
          (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
            (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e))) =
      Sum.inl ((Fin.last H).succ, e) := by
  have hfixed :
      periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H
          (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
            (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)) =
        Sum.inr e := by
    simpa [periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices,
      periodicHypercubicEvenSpatialSliceSumToFixedEdge] using
      (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).apply_symm_apply
        (Sum.inr e)
  simp [periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath,
    hfixed]
  apply Fin.ext
  rfl

private theorem periodicHypercubicEvenPositiveHalfClosureIndexEquiv_interior
    (H : ℕ)
    (k : Fin H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv H
        (Sum.inr
          (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
            (Sum.inl (k, e)))) =
      Sum.inl (k.succ.castSucc, e) := by
  have hopen :
      periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H
          (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
            (Sum.inl (k, e))) =
        Sum.inl (k, e) := by
    simpa [periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex] using
      (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).apply_symm_apply
        (Sum.inl (k, e))
  simp [periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexEquiv,
    periodicHypercubicEvenPositiveHalfBoundaryInteriorSpatialIndexToPath,
    hopen]
  apply Fin.ext
  rfl

private theorem periodicHypercubicEvenPositiveHalfClosureIndexEquiv_temporal
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    periodicHypercubicEvenPositiveHalfClosureIndexEquiv H
        (Sum.inr
          (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
            (Sum.inr (i, v)))) =
      Sum.inr (i, v) := by
  have hopen :
      periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H
          (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
            (Sum.inr (i, v))) =
        Sum.inr (i, v) := by
    simpa [periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex] using
      (periodicHypercubicEvenPositiveEdgeEquivPositiveHalfOpenIndex H).apply_symm_apply
        (Sum.inr (i, v))
  simpa [periodicHypercubicEvenPositiveHalfClosureIndexEquiv,
    periodicHypercubicEvenPositiveHalfClassifiedClosureReassoc,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount, hopen]

/-- At the primary fixed slice, the canonical closure-to-transfer reindexing
reads exactly the corresponding shared-boundary link. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 0 e =
      b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e) := by
  have h := periodicHypercubicEvenPositiveHalfClosureFlat_reindexed_apply
    H N b x
    (Sum.inl (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e))
  rw [periodicHypercubicEvenPositiveHalfClosureIndexEquiv_primary H e] at h
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv] using h

/-- At the antipodal fixed slice, the canonical closure-to-transfer reindexing
reads exactly the second shared-boundary spatial-slice copy. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 (Fin.last H).succ e =
      b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
        (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)) := by
  have h := periodicHypercubicEvenPositiveHalfClosureFlat_reindexed_apply
    H N b x
    (Sum.inl
      (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
        (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e)))
  rw [periodicHypercubicEvenPositiveHalfClosureIndexEquiv_antipodal H e] at h
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv] using h

/-- Every strict interior path layer of the canonical closure reindexing reads
exactly the corresponding positive-edge coordinate. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_interior_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (k : Fin H)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 k.succ.castSucc e =
      x (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
        (Sum.inl (k, e))) := by
  have h := periodicHypercubicEvenPositiveHalfClosureFlat_reindexed_apply
    H N b x
    (Sum.inr
      (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
        (Sum.inl (k, e))))
  rw [periodicHypercubicEvenPositiveHalfClosureIndexEquiv_interior H k e] at h
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatSpatialPathMeasurableEquiv] using h

/-- Every temporal-link layer of the canonical closure reindexing reads exactly
the corresponding positive-edge coordinate. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_temporal_apply
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (v : PeriodicHypercubicEvenSpatialSliceVertex H) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).2 i v =
      x (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
        (Sum.inr (i, v))) := by
  have h := periodicHypercubicEvenPositiveHalfClosureFlat_reindexed_apply
    H N b x
    (Sum.inr
      (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
        (Sum.inr (i, v))))
  rw [periodicHypercubicEvenPositiveHalfClosureIndexEquiv_temporal H i v] at h
  simpa [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatToTransferCoordinatesMeasurableEquiv,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFlatTemporalFieldMeasurableEquiv] using h

/-- The canonical measurable closure reindexing is literally the same spatial
path and temporal-link field obtained by first assembling the positive closure
into a four-dimensional configuration and then restricting that configuration
to the positive cylinder.

This closes the coordinate compatibility needed to transport the OS amplitude
without changing its geometric meaning. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_eq_restrictions
    (H N : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x) =
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1)),
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            b x (fun _ => 1))) := by
  classical
  apply Prod.ext
  · funext j e
    change
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).1 j e =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)) j e
    have hjlt : j.1 < H + 2 := by
      simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using j.2
    by_cases hzero : j.1 = 0
    · have hj : j = 0 := Fin.ext hzero
      rw [hj]
      rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_primary_apply]
      rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_primary]
      unfold periodicHypercubicEvenSpatialSliceRestriction
      unfold periodicHypercubicEvenBoundaryPrimarySpatialSliceConfiguration
      exact
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
          b x (fun _ => 1)
          (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)
    · by_cases hlast : j.1 = H + 1
      · have hj : j = (Fin.last H).succ := by
          apply Fin.ext
          simpa using hlast
        rw [hj]
        rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_antipodal_apply]
        rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction_antipodal]
        unfold periodicHypercubicEvenAntipodalSpatialSliceRestriction
        exact
          (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
            b x (fun _ => 1)
            (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
              (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e))
      · have hjpos : 1 ≤ j.1 := by omega
        have hjle : j.1 ≤ H := by omega
        let k : Fin H := ⟨j.1 - 1, by omega⟩
        have hj : j = k.succ.castSucc := by
          apply Fin.ext
          dsimp [k]
          omega
        rw [hj]
        rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_interior_apply]
        unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
        unfold periodicHypercubicEvenSpecialUnitarySpatialSliceRestrictionAtTime
        unfold periodicHypercubicEvenSpatialSliceLinkAtTime
        change
          x (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
              (Sum.inl (k, e))) =
            (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              b x (fun _ => 1)
              (periodicHypercubicEvenPositiveHalfInteriorSpatialEdge H (k, e))
        exact
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
            b x (fun _ => 1)
            (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
              (Sum.inl (k, e)))).symm
  · funext i v
    change
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
        H N (b, x)).2 i v =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
        H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)) i v
    rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_temporal_apply]
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
    change
      x (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
          (Sum.inr (i, v))) =
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)
          (periodicHypercubicEvenPositiveHalfTemporalEdge H (i, v))
    exact
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_positive
        b x (fun _ => 1)
        (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
          (Sum.inr (i, v)))).symm

/-- Exact Haar transport of the actual OS positive-half amplitude to the nested
spatial-path / temporal-field carrier.  An arbitrary scalar insertion is
transported by the inverse coordinate equivalence and is not discarded. -/
theorem periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_closureIntegral_eq_nestedPathIntegral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ) :
    (∫ z,
      periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
          H N hN beta hbeta z.1 z.2 * F z
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) =
      ∫ q,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta q.1 q.2 *
          F ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N).symm q)
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N) := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H N
  let mu := periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N
  let nu := periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N
  let G := fun q :
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta q.1 q.2 * F (E.symm q)
  have hmp : MeasurePreserving E mu nu := by
    simpa [E, mu, nu] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving
        H N
  calc
    (∫ z,
      periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
          H N hN beta hbeta z.1 z.2 * F z ∂mu) =
        ∫ z,
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
              H N beta (E z).1 (E z).2 * F z ∂mu := by
      apply integral_congr_ae
      filter_upwards with z
      rw [periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_eq_unfixedPathKernel
        H N hN beta hbeta z.1 z.2]
      have hcoord :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_eq_restrictions
          H N z.1 z.2
      have hpath := congrArg Prod.fst hcoord
      have htemporal := congrArg Prod.snd hcoord
      rw [← hpath, ← htemporal]
    _ = ∫ z, G (E z) ∂mu := by
      apply integral_congr_ae
      filter_upwards with z
      simp [G, E]
    _ = ∫ q, G q ∂nu := by
      exact hmp.integral_comp E.measurableEmbedding G
    _ =
      ∫ q,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta q.1 q.2 *
          F ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
            H N).symm q)
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
