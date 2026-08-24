import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCells
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance positiveHalfClosureActionIdentificationSpatialPlaquetteFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
  classical
  infer_instance

local instance positiveHalfClosureActionIdentificationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  infer_instance

local instance positiveHalfClosureActionIdentificationCylinderCellFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H) := by
  classical
  infer_instance

local instance positiveHalfClosureActionIdentificationSupportedPlaquetteFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette H) := by
  classical
  infer_instance

/-- The contribution of one four-dimensional plaquette to the positive-half
closure action.  Writing the three sector indicators additively makes the
subsequent finite reindexing independent of any chosen sector decomposition. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H) : ℝ :=
  let E := specialUnitaryWilsonPlaquetteEnergy N
    (periodicHypercubicPlaquetteHolonomy A p)
  (1 / 2 : ℝ) *
      propositionIndicator (periodicHypercubicEvenSpatialCrossingPlaquette p) E +
    propositionIndicator (periodicHypercubicEvenStrictPositivePlaquette p) E +
    propositionIndicator (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) E

/-- Outside the exact positive-half closure support, the weighted plaquette
energy vanishes. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy_eq_zero_of_not_support
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : ¬ periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport p) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
        H N A p = 0 := by
  have hcross : ¬ periodicHypercubicEvenSpatialCrossingPlaquette p := by
    intro h
    exact hp (Or.inl h)
  have hpositive : ¬ periodicHypercubicEvenStrictPositivePlaquette p := by
    intro h
    exact hp (Or.inr (Or.inl h))
  have hboundary : ¬ periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p := by
    intro h
    exact hp (Or.inr (Or.inr h))
  simp [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy,
    propositionIndicator, hcross, hpositive, hboundary]

/-- The three action sectors occurring in the OS closure definition are one
finite weighted sum over the full plaquette carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSectorAction_eq_sum_weighted
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      ∑ p : PeriodicHypercubicEvenPlaquette H,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
          H N A p := by
  classical
  unfold periodicHypercubicEvenSpatialCrossingWilsonAction
  unfold periodicHypercubicEvenPositiveWilsonAction
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rfl

/-- The full weighted sum is supported exactly on the closure-support subtype. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSum_eq_supportedSum
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∑ p : PeriodicHypercubicEvenPlaquette H,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
          H N A p) =
      ∑ q : PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette H,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
          H N A q.1 := by
  classical
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun p : PeriodicHypercubicEvenPlaquette H =>
        periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport p)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy H N A)
  have hzero :
      (∑ q : {p : PeriodicHypercubicEvenPlaquette H //
          ¬ periodicHypercubicEvenPositiveHalfClosurePlaquetteSupport p},
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
          H N A q.1) = 0 := by
    apply Finset.sum_eq_zero
    intro q _hq
    exact
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy_eq_zero_of_not_support
        H N A q.1 q.2
  rw [hzero, add_zero] at hsplit
  simpa using hsplit.symm

/-- Reindex the supported plaquette sum by the exact finite cylinder-cell
equivalence proved in the preceding geometric unit. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSupportedSum_eq_cellSum
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∑ q : PeriodicHypercubicEvenPositiveHalfClosureSupportedPlaquette H,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
          H N A q.1) =
      ∑ c : PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
          H N A
          (periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding H c) := by
  classical
  symm
  refine Fintype.sum_equiv
    (periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEquiv H) _ _ ?_
  intro c
  rfl

/-- A spatial cylinder cell is a crossing cell exactly at one of the two fixed
end slices. -/
theorem periodicHypercubicEvenPositiveHalfCylinderSpatialCell_spatialCrossing_iff
    (H : ℕ)
    (j : Fin (H + 2))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpatialCrossingPlaquette
        (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
          ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p) ↔
      j.1 = 0 ∨ j.1 = H + 1 := by
  let q := periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
    ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p
  have htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection q :=
    periodicHypercubicEvenSpatialSlicePlaquetteAtTime_not_hasTimeDirection H _ p
  change periodicHypercubicEvenSpatialCrossingPlaquette q ↔ _
  rw [periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane]
  constructor
  · rintro ⟨_htime, hprimary | hantipodal⟩
    · unfold periodicHypercubicEvenOnPrimaryReflectionPlane at hprimary
      have hval := congrArg ZMod.val hprimary
      have hj := periodicHypercubicEvenPositiveHalfCylinderSpatialCell_time_val H j p
      dsimp [q] at hval
      rw [hj] at hval
      change j.1 = 0 at hval
      exact Or.inl hval
    · unfold periodicHypercubicEvenOnAntipodalReflectionPlane at hantipodal
      have hval := congrArg ZMod.val hantipodal
      have hj := periodicHypercubicEvenPositiveHalfCylinderSpatialCell_time_val H j p
      have hhalf_lt : H + 1 < PeriodicHypercubicEvenSideLength H := by
        simp only [PeriodicHypercubicEvenSideLength]
        omega
      dsimp [q] at hval
      rw [hj, ZMod.val_natCast_of_lt hhalf_lt] at hval
      exact Or.inr hval
  · rintro (hzero | hlast)
    · refine ⟨htime, Or.inl ?_⟩
      unfold periodicHypercubicEvenOnPrimaryReflectionPlane
      dsimp [q, periodicHypercubicEvenSpatialSlicePlaquetteAtTime,
        periodicHypercubicEvenSpatialSliceVertexAtTime]
      simpa [hzero]
    · refine ⟨htime, Or.inr ?_⟩
      unfold periodicHypercubicEvenOnAntipodalReflectionPlane
      dsimp [q, periodicHypercubicEvenSpatialSlicePlaquetteAtTime,
        periodicHypercubicEvenSpatialSliceVertexAtTime]
      simpa [hlast]

/-- A spatial cylinder cell lies in the strict positive sector exactly on an
interior spatial slice. -/
theorem periodicHypercubicEvenPositiveHalfCylinderSpatialCell_strictPositive_iff
    (H : ℕ)
    (j : Fin (H + 2))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenStrictPositivePlaquette
        (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
          ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p) ↔
      j.1 ≠ 0 ∧ j.1 ≠ H + 1 := by
  let q := periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
    ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p
  have htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection q :=
    periodicHypercubicEvenSpatialSlicePlaquetteAtTime_not_hasTimeDirection H _ p
  rw [periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection q htime]
  constructor
  · intro hbase
    unfold periodicHypercubicEvenStrictPositiveVertex at hbase
    have hval :=
      (periodicHypercubicEvenStrictPositiveTime_iff_val H (q.1 0)).1 hbase
    have hj := periodicHypercubicEvenPositiveHalfCylinderSpatialCell_time_val H j p
    dsimp [q] at hval
    rw [hj] at hval
    constructor <;> omega
  · rintro ⟨hzero, hlast⟩
    unfold periodicHypercubicEvenStrictPositiveVertex
    rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
    have hj := periodicHypercubicEvenPositiveHalfCylinderSpatialCell_time_val H j p
    dsimp [q]
    rw [hj]
    have hjlt := j.2
    omega

/-- A spatial cylinder cell is never a positive-boundary temporal cell. -/
theorem periodicHypercubicEvenPositiveHalfCylinderSpatialCell_not_positiveBoundaryTemporal
    (H : ℕ)
    (j : Fin (H + 2))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    ¬ periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
      (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
        ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p) := by
  intro h
  exact
    (periodicHypercubicEvenSpatialSlicePlaquetteAtTime_not_hasTimeDirection H _ p) h.1

/-- A temporal cylinder cell is never a spatial crossing cell. -/
theorem periodicHypercubicEvenPositiveHalfCylinderTemporalCell_not_spatialCrossing
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ¬ periodicHypercubicEvenSpatialCrossingPlaquette
      (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) := by
  intro h
  exact h.2
    (periodicHypercubicEvenPositiveHalfTemporalPlaquette_hasTimeDirection H i e)

/-- A temporal cell belongs to the positive-boundary temporal sector exactly
for the first or last slab. -/
theorem periodicHypercubicEvenPositiveHalfCylinderTemporalCell_positiveBoundary_iff
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
        (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) ↔
      i.1 = 0 ∨ i.1 = H := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
  rw [periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val]
  simp [periodicHypercubicEvenPositiveHalfTemporalPlaquette_hasTimeDirection]

/-- A temporal cell is strict-positive exactly for the interior slabs. -/
theorem periodicHypercubicEvenPositiveHalfCylinderTemporalCell_strictPositive_iff
    (H : ℕ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenStrictPositivePlaquette
        (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) ↔
      i.1 ≠ 0 ∧ i.1 ≠ H := by
  let q := periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e
  have htime : periodicHypercubicEvenPlaquetteHasTimeDirection q :=
    periodicHypercubicEvenPositiveHalfTemporalPlaquette_hasTimeDirection H i e
  rw [periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
    q htime]
  constructor
  · rintro ⟨hleft, hright⟩
    have hl := (periodicHypercubicEvenStrictPositiveTime_iff_val H (q.1 0)).1 hleft
    have hr := (periodicHypercubicEvenStrictPositiveTime_iff_val H (q.1 0 + 1)).1 hright
    have hleftval := periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val H i e
    have hrightval := periodicHypercubicEvenPositiveHalfTemporalPlaquette_next_time_val H i e
    dsimp [q] at hl hr
    rw [hleftval] at hl
    rw [hrightval] at hr
    constructor <;> omega
  · rintro ⟨hzero, hlast⟩
    constructor
    · rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
      have hleftval := periodicHypercubicEvenPositiveHalfTemporalPlaquette_time_val H i e
      dsimp [q]
      rw [hleftval]
      have hi := i.2
      simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount] at hi
      omega
    · rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
      have hrightval := periodicHypercubicEvenPositiveHalfTemporalPlaquette_next_time_val H i e
      dsimp [q]
      rw [hrightval]
      have hi := i.2
      simp only [periodicHypercubicEvenPositiveHalfCylinderSlabCount] at hi
      omega

/-- On a spatial cell, the closure weight is one half on the two fixed end
slices and one on every interior slice. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy_spatialCell
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (j : Fin (H + 2))
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy H N A
        (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
          ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p) =
      (if j.1 = 0 ∨ j.1 = H + 1 then (1 / 2 : ℝ) else 1) *
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
              ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p)) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
  rw [periodicHypercubicEvenPositiveHalfCylinderSpatialCell_spatialCrossing_iff]
  rw [periodicHypercubicEvenPositiveHalfCylinderSpatialCell_strictPositive_iff]
  have hboundary :=
    periodicHypercubicEvenPositiveHalfCylinderSpatialCell_not_positiveBoundaryTemporal H j p
  by_cases hend : j.1 = 0 ∨ j.1 = H + 1
  · have hend' : j = 0 ∨ j.1 = H + 1 := by
      rcases hend with hzero | hlast
      · exact Or.inl (Fin.ext hzero)
      · exact Or.inr hlast
    have hinterior' : ¬ (¬ j = 0 ∧ j.1 ≠ H + 1) := by
      tauto
    simp [propositionIndicator, hend, hend', hinterior', hboundary]
  · have hend' : ¬ (j = 0 ∨ j.1 = H + 1) := by
      intro h
      apply hend
      rcases h with hzero | hlast
      · exact Or.inl (congrArg Fin.val hzero)
      · exact Or.inr hlast
    have hinterior' : ¬ j = 0 ∧ j.1 ≠ H + 1 := by
      tauto
    simp [propositionIndicator, hend, hend', hinterior', hboundary]

/-- Every temporal cell has total closure weight one: endpoint temporal cells
come from the boundary-temporal sector, while interior cells come from the
strict-positive sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy_temporalCell
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy H N A
        (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e) =
      specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e)) := by
  classical
  have hcross :=
    periodicHypercubicEvenPositiveHalfCylinderTemporalCell_not_spatialCrossing H i e
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy
  rw [periodicHypercubicEvenPositiveHalfCylinderTemporalCell_positiveBoundary_iff]
  rw [periodicHypercubicEvenPositiveHalfCylinderTemporalCell_strictPositive_iff]
  by_cases hend : i.1 = 0 ∨ i.1 = H
  · have hinterior : ¬ (i.1 ≠ 0 ∧ i.1 ≠ H) := by
      tauto
    simp [propositionIndicator, hcross, hend, hinterior]
  · have hinterior : i.1 ≠ 0 ∧ i.1 ≠ H := by
      tauto
    simp [propositionIndicator, hcross, hend, hinterior]

/-- Fintype sum form of the intrinsic one-slice spatial Wilson action. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_fintypeSum
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := by
  classical
  simp [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
    periodicHypercubicEvenSpatialSlicePlaquetteList]

/-- Fintype sum form of the one-slab unfixed temporal crossing action. -/
theorem periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction_eq_fintypeSum
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (U : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction H N A U B =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        specialUnitaryWilsonPlaquetteEnergy N
          ((A e)⁻¹ * U e.1 * B e *
            (U (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹) := by
  classical
  simp [periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction,
    periodicHypercubicEvenSpatialSliceLinkList]

/-- The spatial part of one fixed cylinder slice is its endpoint/interior
coefficient times the intrinsic spatial Wilson action. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSpatialLayerSum
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (j : Fin (H + 2)) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy H N A
        (periodicHypercubicEvenSpatialSlicePlaquetteAtTime H
          ((j.1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) p)) =
      (if j.1 = 0 ∨ j.1 = H + 1 then (1 / 2 : ℝ) else 1) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
            H N A j) := by
  classical
  simp_rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy_spatialCell]
  simp_rw [periodicHypercubicEvenSpatialSlicePlaquetteEnergy_restrictionAtTime_eq]
  rw [← Finset.mul_sum]
  rw [← periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_fintypeSum]
  rfl

/-- The temporal cells in one slab sum to the exact unfixed temporal crossing
action of that slab. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTemporalLayerSum
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy H N A
        (periodicHypercubicEvenPositiveHalfTemporalPlaquette H i e)) =
      periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A i.castSucc)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction
          H N A i)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction
          H N A i.succ) := by
  classical
  simp_rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy_temporalCell]
  simp_rw [periodicHypercubicEvenPositiveHalfTemporalPlaquette_energy_eq_unfixed]
  rw [periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction_eq_fintypeSum]

/-- Elementary finite-path bookkeeping: assigning half weight to the two end
slices and full weight to every interior slice is the same as assigning one
half to each endpoint of every adjacent slab. -/
private theorem positiveHalf_endpointHalfSum_eq_adjacentHalfSum
    (H : ℕ)
    (F : Fin (H + 2) → ℝ) :
    (∑ j : Fin (H + 2),
      (if j.1 = 0 ∨ j.1 = H + 1 then (1 / 2 : ℝ) else 1) * F j) =
      ∑ i : Fin (H + 1),
        ((1 / 2 : ℝ) * F i.castSucc + (1 / 2 : ℝ) * F i.succ) := by
  classical
  let G : Fin (H + 2) → ℝ := fun j =>
    (if j.1 = 0 ∨ j.1 = H + 1 then (1 / 2 : ℝ) else 1) * F j
  have hmiddleWeight (k : Fin H) : G k.castSucc.succ = F k.castSucc.succ := by
    dsimp [G]
    have hk := k.2
    have hend : ¬ (k.1 + 1 = 0 ∨ k.1 + 1 = H + 1) := by
      omega
    rw [if_neg hend]
    ring
  have hzeroWeight : G (0 : Fin (H + 2)) = (1 / 2 : ℝ) * F 0 := by
    simp [G]
  have hlastWeight :
      G (Fin.last H).succ = (1 / 2 : ℝ) * F (Fin.last H).succ := by
    simp [G]
  have hleft :
      (∑ j : Fin (H + 2), G j) =
        (1 / 2 : ℝ) * F 0 +
          (∑ k : Fin H, F k.castSucc.succ) +
          (1 / 2 : ℝ) * F (Fin.last H).succ := by
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_castSucc]
    rw [hzeroWeight, hlastWeight]
    simp_rw [hmiddleWeight]
    ring
  have hfirst :
      (∑ i : Fin (H + 1), (1 / 2 : ℝ) * F i.castSucc) =
        (1 / 2 : ℝ) * F 0 +
          ∑ k : Fin H, (1 / 2 : ℝ) * F k.castSucc.succ := by
    rw [Fin.sum_univ_succ]
    congr 1
  have hsecond :
      (∑ i : Fin (H + 1), (1 / 2 : ℝ) * F i.succ) =
        (∑ k : Fin H, (1 / 2 : ℝ) * F k.castSucc.succ) +
          (1 / 2 : ℝ) * F (Fin.last H).succ := by
    rw [Fin.sum_univ_castSucc]
  have hdouble :
      (∑ k : Fin H, (1 / 2 : ℝ) * F k.castSucc.succ) +
          (∑ k : Fin H, (1 / 2 : ℝ) * F k.castSucc.succ) =
        ∑ k : Fin H, F k.castSucc.succ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  change (∑ j : Fin (H + 2), G j) = _
  rw [hleft]
  rw [Finset.sum_add_distrib, hfirst, hsecond]
  rw [← hdouble]
  ring

/-- The complete weighted cylinder-cell sum is literally the unfixed path
action read from the same four-dimensional configuration. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureCellSum_eq_unfixedPathAction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∑ c : PeriodicHypercubicEvenPositiveHalfCylinderPlaquetteCell H,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureWeightedPlaquetteEnergy H N A
        (periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding H c)) =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction H N A)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction H N A) := by
  classical
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [periodicHypercubicEvenPositiveHalfCylinderPlaquetteCellEmbedding]
  simp_rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSpatialLayerSum]
  simp_rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTemporalLayerSum]
  rw [positiveHalf_endpointHalfSum_eq_adjacentHalfSum H
    (fun j =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction H N A j))]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
  unfold periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction
  simp only [Finset.sum_add_distrib]
  ring

/-- Main action identification: the actual OS positive-half closure action is
exactly the unfixed finite-cylinder path action of its spatial and temporal
restrictions. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSectorAction_eq_unfixedPathAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (1 / 2 : ℝ) * periodicHypercubicEvenSpatialCrossingWilsonAction H N A +
        periodicHypercubicEvenPositiveWilsonAction H N A +
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction H N A)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction H N A) := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSectorAction_eq_sum_weighted]
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSum_eq_supportedSum]
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSupportedSum_eq_cellSum]
  exact periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureCellSum_eq_unfixedPathAction H N A

/-- Specialization of the action identification to the boundary/open-half
coordinates used by the completed OS Gram feature. -/
theorem periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction_eq_unfixedPathAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction H N b x =
      let A :=
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x (fun _ => 1)
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction H N
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPathRestriction H N A)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalFieldRestriction H N A) := by
  unfold periodicHypercubicEvenBoundaryPositiveHalfClosureWilsonAction
  exact
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureSectorAction_eq_unfixedPathAction H N
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
        b x (fun _ => 1))

end

end MathlibAnalytic
end MGAP4D