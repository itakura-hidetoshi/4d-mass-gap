import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryTemporalCompanionOpenPathSection
import Mathlib.Tactic.FunProp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance primaryTemporalCompanionCoordinatesTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

/-- Each canonical primary temporal-companion open path is literally the
product of its three positive-open-half coordinates: the lower temporal edge,
the independently selected upper spatial edge, and the inverse upper temporal
edge.  No boundary or negative-half coordinate remains. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionFiberedOpenPath_eq_coordinates
    (H N : ℕ) (hH : 0 < H)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (k : Fin 4) :
    periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k) =
      x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
          H hH k) *
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH k) *
        (x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
          H hH k))⁻¹ := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k
  let A := P.boundaryFiberedAssemble
    (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
  have hbase : (p.1 0).val = 0 := by
    change ((periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1 0).val = 0
    exact periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k
  have hA0 :
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 0).edge =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
          H hH k) := by
    exact P.boundaryFiberedAssemble_positive
      (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
        H hH k)
  have hA1 :
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 1).edge =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH k) := by
    exact P.boundaryFiberedAssemble_positive
      (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
        H hH k)
  have hA2 :
      A (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 2).edge =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
          H hH k) := by
    exact P.boundaryFiberedAssemble_positive
      (fun _ => (1 : Gauge)) x (fun _ => (1 : Gauge))
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
        H hH k)
  have hs0 :
      periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 0) =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
          H hH k) := by
    change A (periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p 0).edge = _
    exact hA0
  have hs1 :
      periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 1) =
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH k) := by
    change A (periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p 1).edge = _
    exact hA1
  have hs2 :
      periodicHypercubicStepValue A
          (periodicHypercubicBoundaryStep
            (PeriodicHypercubicEvenSideLength H) p 2) =
        (x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
          H hH k))⁻¹ := by
    change (A (periodicHypercubicBoundaryStep
      (PeriodicHypercubicEvenSideLength H) p 2).edge)⁻¹ = _
    rw [hA2]
  change periodicHypercubicEvenPositiveBoundaryTemporalOpenPath A p = _
  unfold periodicHypercubicEvenPositiveBoundaryTemporalOpenPath
  rw [if_pos hbase, hs0, hs1, hs2]

/-- Consequently each primary temporal-companion open path is continuous on
the genuine positive-open-half product topology.  This is the topological
input needed to turn a section-level nonzero Fock probe into a nonzero Haar
`L²` vector. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionFiberedOpenPath_continuous
    (H N : ℕ) (hH : 0 < H) (k : Fin 4) :
    Continuous
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) := by
  have h0 : Continuous
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
          H hH k)) :=
    continuous_apply _
  have h1 : Continuous
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
          H hH k)) :=
    continuous_apply _
  have h2 : Continuous
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
          H hH k)) :=
    continuous_apply _
  have hcoordinates : Continuous
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
            H hH k) *
          x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
            H hH k) *
          (x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
            H hH k))⁻¹) :=
    (h0.mul h1).mul h2.inv
  have hfun :
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)) =
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepZeroPositiveEdge
            H hH k) *
          x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionUpperSpatialEdgeEmbedding
            H hH k) *
          (x (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionStepTwoPositiveEdge
            H hH k))⁻¹) := by
    funext x
    exact
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionFiberedOpenPath_eq_coordinates
        H N hH x k
  rw [hfun]
  exact hcoordinates

end

end MathlibAnalytic
end MGAP4D