import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundarySpatialEndpointWeights
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance osBoundarySpatialHalfWeightSpatialSlicePlaquetteFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  Fintype.ofFinite _

local instance osBoundarySpatialHalfWeightSpatialCrossingPlaquetteFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype H) :=
  Fintype.ofFinite _

/-- Read the primary reflection-fixed spatial slice directly from a boundary
configuration. -/
def periodicHypercubicEvenBoundaryPrimarySpatialSliceConfiguration
    (H : ℕ)
    {Value : Type*}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value) :
    PeriodicHypercubicEvenSpatialSliceConfiguration H Value :=
  fun e => b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)

/-- Read the antipodal reflection-fixed spatial slice from the same boundary,
canonically reindexed by the half-period equivalence back to the primary slice
link carrier. -/
def periodicHypercubicEvenBoundaryAntipodalSpatialSliceConfiguration
    (H : ℕ)
    {Value : Type*}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value) :
    PeriodicHypercubicEvenSpatialSliceConfiguration H Value :=
  fun e =>
    b (periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H
      (periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e))

/-- Restriction of a full four-dimensional configuration to the antipodal fixed
slice, reindexed on the canonical primary spatial link carrier. -/
def periodicHypercubicEvenAntipodalSpatialSliceRestriction
    {H : ℕ} {Gauge : Type}
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenSpatialSliceConfiguration H Gauge :=
  fun e =>
    A (periodicHypercubicEvenHalfPeriodTimeShift H e.1.1, e.2.1)

/-- Half-period translation commutes with every spatial unit shift. -/
theorem periodicHypercubicEvenHalfPeriodTimeShift_shift_spatial
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H)
    (mu : PeriodicHypercubicAxis)
    (hmu : mu ≠ 0) :
    periodicHypercubicEvenHalfPeriodTimeShift H
        (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H) v mu) =
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenHalfPeriodTimeShift H v) mu := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [periodicHypercubicEvenHalfPeriodTimeShift,
      periodicHypercubicShift_apply, hmu, Ne.symm hmu]
  · simp [periodicHypercubicEvenHalfPeriodTimeShift,
      periodicHypercubicShift_apply, hi]

/-- Intrinsic plaquette holonomy of the antipodal restriction is exactly the
four-dimensional holonomy of the corresponding antipodal embedded plaquette. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_antipodalRestriction_eq
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (periodicHypercubicEvenAntipodalSpatialSliceRestriction A) p =
      periodicHypercubicPlaquetteHolonomy A
        (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p) := by
  unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
  unfold periodicHypercubicEvenAntipodalSpatialSliceRestriction
  unfold periodicHypercubicPlaquetteHolonomy
  simp only [periodicHypercubicBoundaryStep_zero,
    periodicHypercubicBoundaryStep_one,
    periodicHypercubicBoundaryStep_two,
    periodicHypercubicBoundaryStep_three,
    periodicHypercubicStepValue]
  unfold periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding
  simp only [periodicHypercubicPlaquetteFirstAxis,
    periodicHypercubicPlaquetteSecondAxis]
  rw [← periodicHypercubicEvenHalfPeriodTimeShift_shift_spatial
    H p.1.1 p.2.1.1.1 p.2.1.1.2]
  rw [← periodicHypercubicEvenHalfPeriodTimeShift_shift_spatial
    H p.1.1 p.2.1.2.1 p.2.1.2.2]

/-- Boundary-fibered assembly restricted to the primary fixed spatial slice
recovers the primary boundary slice exactly. -/
theorem periodicHypercubicEvenBoundaryFiberedAssemble_primarySpatialSliceRestriction
    (H : ℕ)
    {Value : Type*}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value) :
    periodicHypercubicEvenSpatialSliceRestriction
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      periodicHypercubicEvenBoundaryPrimarySpatialSliceConfiguration H b := by
  funext e
  change
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y
        (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e).1 =
      b (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)
  exact (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
    b x y (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H e)

/-- Boundary-fibered assembly restricted to the antipodal fixed spatial slice
recovers the antipodal boundary slice exactly. -/
theorem periodicHypercubicEvenBoundaryFiberedAssemble_antipodalSpatialSliceRestriction
    (H : ℕ)
    {Value : Type*}
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value) :
    periodicHypercubicEvenAntipodalSpatialSliceRestriction
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      periodicHypercubicEvenBoundaryAntipodalSpatialSliceConfiguration H b := by
  funext e
  let ea := periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv H e
  let fe := periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge H ea
  have hfixed :=
    (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble_fixed
      b x y fe
  simpa [periodicHypercubicEvenAntipodalSpatialSliceRestriction,
    periodicHypercubicEvenBoundaryAntipodalSpatialSliceConfiguration,
    ea, fe,
    periodicHypercubicEvenPrimaryAntipodalSpatialSliceLinkEquiv,
    periodicHypercubicEvenPrimaryToAntipodalSpatialSliceVertex,
    periodicHypercubicEvenAntipodalSpatialSliceLinkToFixedEdge] using hfixed

/-- An indicator sum over a finite carrier is exactly the corresponding sum
over its satisfying subtype. -/
private theorem fintype_sum_propositionIndicator_eq_subtype
    {ι : Type*} [Fintype ι]
    (P : ι → Prop)
    (f : ι → ℝ) :
    (∑ i : ι, propositionIndicator (P i) (f i)) =
      ∑ i : {i // P i}, f i := by
  classical
  calc
    (∑ i : ι, propositionIndicator (P i) (f i)) =
        ∑ i ∈ (Finset.univ.filter P : Finset ι), f i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      simp [propositionIndicator]
    _ = ∑ i : {i // P i}, f i := by
      exact Finset.sum_subtype
        (Finset.univ.filter P) (fun i => by simp) f

/-- The complete purely-spatial crossing action is the sum of the Wilson
actions on the primary and antipodal fixed spatial slices.  This statement is
valid for an arbitrary full configuration; no boundary-fibered hypothesis is
needed. -/
theorem periodicHypercubicEvenSpatialCrossingWilsonAction_eq_primary_add_antipodal
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialCrossingWilsonAction H N A =
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpatialSliceRestriction A) +
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenAntipodalSpatialSliceRestriction A) := by
  classical
  let energy := fun p : PeriodicHypercubicEvenPlaquette H =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicPlaquetteHolonomy A p)
  let crossEnergy := fun p : PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype H =>
    energy p.1
  let E := periodicHypercubicEvenSpatialCrossingPlaquetteEquivTwoSpatialSlices H
  have hsub :
      periodicHypercubicEvenSpatialCrossingWilsonAction H N A =
        ∑ p : PeriodicHypercubicEvenSpatialCrossingPlaquetteSubtype H,
          crossEnergy p := by
    unfold periodicHypercubicEvenSpatialCrossingWilsonAction
    simpa [energy, crossEnergy] using
      fintype_sum_propositionIndicator_eq_subtype
        (fun p : PeriodicHypercubicEvenPlaquette H =>
          periodicHypercubicEvenSpatialCrossingPlaquette p) energy
  rw [hsub]
  have hreindex := E.symm.sum_comp crossEnergy
  rw [← hreindex]
  rw [Fintype.sum_sum_type]
  unfold crossEnergy energy E
  simp only [Equiv.symm_apply_apply]
  have hprimary :
      (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p))) =
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (periodicHypercubicEvenSpatialSliceRestriction A) := by
    simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
      periodicHypercubicEvenSpatialSlicePlaquetteList] using
      congrArg List.sum
        (congrArg
          (List.map (specialUnitaryWilsonPlaquetteEnergy N))
          (by
            apply List.ext_get
            · simp [periodicHypercubicEvenSpatialSlicePlaquetteList]
            · intro n hn₁ hn₂
              simp only [List.get_map]
              rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_restriction_eq]))
  have hantipodal :
      (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenAntipodalSpatialSlicePlaquetteEmbedding H p))) =
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (periodicHypercubicEvenAntipodalSpatialSliceRestriction A) := by
    simpa [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
      periodicHypercubicEvenSpatialSlicePlaquetteList] using
      congrArg List.sum
        (congrArg
          (List.map (specialUnitaryWilsonPlaquetteEnergy N))
          (by
            apply List.ext_get
            · simp [periodicHypercubicEvenSpatialSlicePlaquetteList]
            · intro n hn₁ hn₂
              simp only [List.get_map]
              rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_antipodalRestriction_eq]))
  simpa [periodicHypercubicEvenSpatialCrossingPlaquetteEquivTwoSpatialSlices,
    periodicHypercubicEvenTwoSpatialSlicesToSpatialCrossingPlaquette] using
    congrArg₂ (· + ·) hprimary hantipodal

/-- Specializing the general fixed-plane decomposition to a boundary-fibered
configuration makes both summands depend only on the two boundary slices. -/
theorem periodicHypercubicEvenBoundarySpatialCrossingWilsonAction_eq_endpointSlices
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpatialCrossingWilsonAction H N
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b (fun _ => 1) (fun _ => 1)) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenBoundaryPrimarySpatialSliceConfiguration H b) +
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenBoundaryAntipodalSpatialSliceConfiguration H b) := by
  rw [periodicHypercubicEvenSpatialCrossingWilsonAction_eq_primary_add_antipodal]
  rw [periodicHypercubicEvenBoundaryFiberedAssemble_primarySpatialSliceRestriction]
  rw [periodicHypercubicEvenBoundaryFiberedAssemble_antipodalSpatialSliceRestriction]

/-- The OS square-root boundary spatial weight is exactly the product of the
two endpoint half-weights appearing in the symmetric one-slab transfer kernel. -/
theorem periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_sqrt_eq_endpointHalfWeights
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.sqrt
        (periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight
          H N beta b) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta
          (periodicHypercubicEvenBoundaryPrimarySpatialSliceConfiguration H b) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta
          (periodicHypercubicEvenBoundaryAntipodalSpatialSliceConfiguration H b) := by
  rw [periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight_sqrt_eq_halfAction]
  rw [periodicHypercubicEvenBoundarySpatialCrossingWilsonAction_eq_endpointSlices]
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  rw [← Real.exp_add]
  congr 1
  ring

end

end MathlibAnalytic
end MGAP4D
