import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicOriginalOSCenteredKernelPhysicalFactorizationV5_PZ37APT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualCanonicalCompletedBoundarySpatialSlicePairL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APU — exact coordinate seam for completed OS and original insertion
The automatic completed OS realization and APT's original centered kernel
use the same literal pair Haar coordinate map. If the original centered
moment has a completed OS representative, the representative determines
the genuine inserted operator, with its norm bounded by the OS state norm.
Realization of the moment and genuine time translation are separate obligations.
-/
namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "L" => PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2
local notation "J" => periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
local notation "J0" => periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "U" => p4Q2PZ37APP_originalTimeOneOSCenteredBoundaryL2
local notation "Vac" => periodicHypercubicEvenBoundaryVacuumL2
local notation "A" => p4Q2PZ37APR_originalCenteredBoundaryKernelOperator
local notation "C" => p4Q2PZ37APT_originalCenteredPhysicalInsertion

local instance p4Q2PZ37APU_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APU_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APU_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APU_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APU_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APU_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APU_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APU_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37APU_sliceFinite (H : ℕ) : SFinite (Mu H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance


theorem p4Q2PZ37APU_boundaryPairCoordinateIsometries_apply
    (H : ℕ) (f : L H 2) :
    J H 2 f = J0 H 2 f := by
  apply Lp.ext
  exact (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
    H 2 f).trans
    (periodicHypercubicEvenSpecialUnitaryBoundaryL2ToSpatialSlicePairL2_coeFn H 2 f).symm

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {halfExtent : ℕ → ℕ} {hN : 0 < (2 : ℕ)}
    [Nontrivial G] {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalFiberReflection
      S halfExtent 2 hN beta hbeta)

theorem p4Q2PZ37APU_completedSpatialPair_eq_boundaryTransport
    (n : ℕ) (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert) :
    R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n x =
      J (halfExtent n) 2 (R.toCompletedBoundaryMomentLinearIsometryAutomatic n x) := by
  change J0 (halfExtent n) 2 (R.toCompletedBoundaryMomentLinearIsometryAutomatic n x) = _
  exact (p4Q2PZ37APU_boundaryPairCoordinateIsometries_apply (halfExtent n)
    (R.toCompletedBoundaryMomentLinearIsometryAutomatic n x)).symm

theorem p4Q2PZ37APU_centeredRealization_iff
    (n : ℕ) (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert) :
    R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n x =
      J (halfExtent n) 2 (U (halfExtent n) (beta n) (hbeta n)) ↔
    R.toCompletedBoundaryMomentLinearIsometryAutomatic n x =
      U (halfExtent n) (beta n) (hbeta n) := by
  rw [p4Q2PZ37APU_completedSpatialPair_eq_boundaryTransport R n x]
  constructor
  · intro hx
    exact (J (halfExtent n) 2).injective hx
  · intro hx
    rw [hx]

theorem p4Q2PZ37APU_centeredKernel_eq_of_completedRealization
    (n : ℕ) (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert)
    (hx : R.toCompletedBoundaryMomentLinearIsometryAutomatic n x =
      U (halfExtent n) (beta n) (hbeta n)) :
    realL2HilbertSchmidtKernelOperator (μ := Mu (halfExtent n) 2)
      (R.toCompletedSpatialSlicePairMomentLinearIsometryAutomatic n x) =
      A (halfExtent n) (beta n) (hbeta n) := by
  rw [p4Q2PZ37APU_completedSpatialPair_eq_boundaryTransport R n x, hx]
  rfl

theorem p4Q2PZ37APU_physicalInsertion_norm_le_of_completedRealization
    (n : ℕ) (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert)
    (hx : R.toCompletedBoundaryMomentLinearIsometryAutomatic n x =
      U (halfExtent n) (beta n) (hbeta n)) :
    ‖C (halfExtent n) (beta n) (hbeta n)‖ ≤ ‖x‖ := by
  calc
    ‖C (halfExtent n) (beta n) (hbeta n)‖ =
        ‖A (halfExtent n) (beta n) (hbeta n)‖ :=
      (p4Q2PZ37APT_originalCenteredBoundaryKernelOperator_norm_eq_physical
        (halfExtent n) (beta n) (hbeta n)).symm
    _ ≤ ‖U (halfExtent n) (beta n) (hbeta n)‖ :=
      p4Q2PZ37APR_originalCenteredBoundaryKernelOperator_norm_le
        (halfExtent n) (beta n) (hbeta n)
    _ = ‖x‖ := by
      rw [← hx]
      exact (R.toCompletedBoundaryMomentLinearIsometryAutomatic n).norm_map x

theorem p4Q2PZ37APU_completedRealization_orthogonal_of_vacuumRealization
    (n : ℕ) (x v : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S R.reflectionData halfExtent 2 hN beta hbeta
        R.toLinearHalfSupportReflection.toCommonPositiveHalfPullback.toWeakStarBridge
        R.approximatingReflectionInvariantFamily n).PhysicalHilbert)
    (hx : R.toCompletedBoundaryMomentLinearIsometryAutomatic n x =
      U (halfExtent n) (beta n) (hbeta n))
    (hv : R.toCompletedBoundaryMomentLinearIsometryAutomatic n v =
      Vac (halfExtent n) 2 hN (beta n) (hbeta n)) :
    inner ℝ v x = 0 := by
  calc
    inner ℝ v x =
        inner ℝ (R.toCompletedBoundaryMomentLinearIsometryAutomatic n v)
          (R.toCompletedBoundaryMomentLinearIsometryAutomatic n x) :=
      ((R.toCompletedBoundaryMomentLinearIsometryAutomatic n).inner_map_map v x).symm
    _ = 0 := by
      rw [hv, hx]
      exact p4Q2PZ37APP_originalTimeOneOSCenteredBoundaryL2_orthogonal
        (halfExtent n) (beta n) (hbeta n)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APU_boundaryPairCoordinateIsometries_apply
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APU_completedSpatialPair_eq_boundaryTransport
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APU_centeredRealization_iff
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APU_centeredKernel_eq_of_completedRealization
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APU_physicalInsertion_norm_le_of_completedRealization
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APU_completedRealization_orthogonal_of_vacuumRealization
