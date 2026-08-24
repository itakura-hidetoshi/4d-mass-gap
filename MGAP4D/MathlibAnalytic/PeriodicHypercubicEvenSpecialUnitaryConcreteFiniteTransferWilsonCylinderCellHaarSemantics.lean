import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonWordHaarSemantics
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000

local instance wilsonCylinderCellHaarSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderCellHaarSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderCellHaarSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderCellHaarSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderCellHaarSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderCellHaarSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderCellHaarSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The complete symmetric one-slab Wilson action, regarded as one bounded
continuous observable of the two adjacent spatial boundaries.

This is the actual local Wilson cylinder cell
`(1/2) S_spatial(A) + S_cross(A,B) + (1/2) S_spatial(B)`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairBoundedObservable H N :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
          H N p.1 p.2,
      by
        have hleft : Continuous
            (fun p :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
              periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N p.1) :=
          (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable
            H N).continuous.comp continuous_fst
        have hcross : Continuous
            (fun p :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
                H N p.1 p.2) :=
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H N
        have hright : Continuous
            (fun p :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
              periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N p.2) :=
          (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable
            H N).continuous.comp continuous_snd
        unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
        exact ((continuous_const.mul hleft).add hcross).add
          (continuous_const.mul hright)⟩

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_apply
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
        H N (A, B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B :=
  rfl

/-- The bounded cylinder-cell observable is simultaneously gauge invariant on
its two spatial boundaries. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_gaugeInvariant
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairObservableGaugeInvariant H N
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
        H N) := by
  intro γ A B
  change
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ A)
        (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H N γ B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant H N γ A]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_gaugeInvariant H N γ A B]
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant H N γ B]

/-- Audit-visible local decomposition of the actual one-slab cylinder cell into
its two spatial half-actions and temporal crossing action. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_eq_localWilsonGenerators
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B =
      (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A +
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B +
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B := by
  rfl

/-- Chronological transfer word carrying one complete actual Wilson cylinder
cell after `left` and before `right` ordinary transfers.  It consumes one slab,
just like any adjacent-slice insertion. -/
def periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
    (H N left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord
    H N left right
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
      H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_gaugeInvariant
      H N)

/-- A cylinder-cell word has the expected fixed total slab count. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord_slabCount
    (H N left right : ℕ) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
          H N left right) =
      left + right + 1 := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord] using
    (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_slabCount
      H N left right
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
        H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_gaugeInvariant
        H N))

/-- Genuine Gauss-law operator for one complete Wilson cylinder-cell insertion
at an arbitrary transfer slab. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabPairObservableOperator
    H N hN beta hbeta left right
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
      H N)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_gaugeInvariant
      H N)

/-- The cylinder-cell transfer word evaluates to the corresponding genuine
physical arbitrary-slab insertion operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWordPhysicalOperator_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
          H N left right) =
      periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
        H N hN beta hbeta left right := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord,
    periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator] using
    (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWordPhysicalOperator_eq
      H N hN beta hbeta left right
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
        H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_gaugeInvariant
        H N))

/-- Operator semantics of the complete Wilson cylinder-cell word. -/
theorem
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord_haarAmplitude_eq_operator_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
          H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
          H N hN beta hbeta left right f) g := by
  calc
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
          H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
            H N left right) f) g := by
      symm
      exact
        periodicHypercubicEvenSpecialUnitaryFiniteTransferWordPhysicalOperator_inner_eq_haarAmplitude
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
            H N left right) f g
    _ = inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalTransferSlabWilsonCylinderCellActionOperator
          H N hN beta hbeta left right f) g := by
      rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWordPhysicalOperator_eq]

/-- Literal Haar semantics of one complete Wilson cylinder cell.  The inserted
factor is exactly the actual symmetric one-slab Wilson action, not an abstract
proxy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord_haarAmplitude_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordHaarAmplitude H N beta
        (periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
          H N left right)
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryNSlabSpatialPath
          H N (left + right + 1),
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePathKernel
            H N beta (left + right + 1) path *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N
            (path (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right).castSucc)
            (path (periodicHypercubicEvenSpecialUnitaryTransferSlabIndex left right).succ) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (left + right + 1)))
        ∂(periodicHypercubicEvenSpecialUnitaryNSlabSpatialPathHaarMeasure
          H N (left + right + 1)) := by
  simpa [periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord,
    periodicHypercubicEvenSpecialUnitaryTransferSlabPairObservableAmplitude,
    periodicHypercubicEvenSpecialUnitaryNSlabTemporalGaugePairObservableAmplitude] using
    (periodicHypercubicEvenSpecialUnitaryFiniteTransferSlabInsertionWord_haarAmplitude_eq_amplitude
      H N hN beta hbeta left right
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
        H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable_gaugeInvariant
        H N) f g)

/-- On an actual positive-half-cylinder path, the existing cylinder action is
literally the finite sum of the bounded local cell observables promoted above
to transfer-word letters. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_eq_sum_cellObservable
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
        H N path =
      ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabActionBoundedPairObservable
          H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- Expanded cylinder-action decomposition into the actual left spatial
half-action, temporal crossing action, and right spatial half-action on every
positive-half slab. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_eq_sum_localWilsonGenerators
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
        H N path =
      ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        ((1 / 2 : ℝ) *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i) +
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabLeft path i)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i) +
          (1 / 2 : ℝ) *
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderPathSlabRight path i)) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- The cell at positive-half slab `i` is represented by a transfer word whose
slab count is exactly the full positive-half-cylinder length. -/
def periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord
    (H N : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteTransferWord H N :=
  periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord
    H N i.1 (H - i.1)

/-- Every positive-half cell word lives on the same `H+1`-slab path carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord_slabCount
    (H N : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    periodicHypercubicEvenSpecialUnitaryFiniteTransferWordSlabCount
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord H N i) =
      periodicHypercubicEvenPositiveHalfCylinderSlabCount H := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderWilsonCellWord
  rw [periodicHypercubicEvenSpecialUnitaryFiniteTransferWilsonCylinderCellWord_slabCount]
  unfold periodicHypercubicEvenPositiveHalfCylinderSlabCount
  have hi : i.1 ≤ H := by
    have hlt : i.1 < H + 1 := by
      simpa [periodicHypercubicEvenPositiveHalfCylinderSlabCount] using i.2
    omega
  omega

end
end MathlibAnalytic
end MGAP4D