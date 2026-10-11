import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarAllCoordinateCommonFixedCollapse
import Mathlib.Tactic

/-!
# P4-Q2-CT: pair-Haar projection commutation reduced to actual Haar retention

CR built true pair-Haar coordinate-exclusion orthogonal projections P_i.
CS proved their joint fixed sector consists of physical pair-Haar-a.e.
constants. CQ proved tensorization for commuting orthogonal projections.

Here is the missing OPERATOR reduction, with no phantom Fubini step:
for self-adjoint real-Hilbert projections P and Q, if P maps the
Q-fixed sector into the Q-fixed sector, then P and Q commute.
Only ONE directed invariance assumption is needed; orthogonality
supplies the converse direction without a second hypothesis.

For actual independent pair-Haar L² coordinate projections this reduces
commutation to a concrete statement: after removing coordinate j,
averaging coordinate i preserves sigma-measurability without j.
The latter is an EXACT sigma-algebra/independent-Haar-Fubini
measurability obligation, left visibly as a premise.

Using the reduction, give the actual CQ tensorization and CS
constant-sweep theorem under the one-sided *retained measurability*
assumption, not under an arbitrary commutation oracle.

The positive-beta Wilson joint conditional expectations are NEVER
assumed to commute. This is not yet an unconditional Haar
Efron--Stein inequality, volume-uniform Wilson gap, or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

/-- If a self-adjoint projection P preserves Q's fixed range and Q is
self-adjoint, then P and Q COMMUTE. We prove it from Hilbert matrix
elements, avoiding any hidden finite-dimensional assumption. -/
theorem p4Q2CT_symmetricProjections_commute_of_fixedInvariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E)
    (hPsym : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hQsym : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (hQid : ∀ x, Q (Q x) = Q x)
    (hStable : ∀ x, Q (P (Q x)) = P (Q x))
    (x : E) :
    P (Q x) = Q (P x) := by
  apply ext_inner_right ℝ
  intro y
  calc
    inner ℝ (P (Q x)) y =
        inner ℝ (Q (P (Q x))) y := by rw [hStable x]
    _ = inner ℝ (P (Q x)) (Q y) := hQsym (P (Q x)) y
    _ = inner ℝ (Q x) (P (Q y)) := hPsym (Q x) (Q y)
    _ = inner ℝ x (Q (P (Q y))) := by rw [hQsym x (P (Q y)), hStable y]
    _ = inner ℝ x (P (Q y)) := by rw [hStable y]
    _ = inner ℝ (P x) (Q y) := (hPsym x (Q y)).symm
    _ = inner ℝ (Q (P x)) y := (hQsym (P x) y).symm

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualPairHaar
variable (H N : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- Actual pair-Haar projection commutation follows from JUST the directed
sigma-algebra retention assertion on the actual Haar L². This retention
is the remaining direct Fubini obligation, not an extra property of the
interacting Wilson measure. -/
theorem p4Q2CT_actualPairHaarProjection_commute_of_retainedMeasurability
    (i j : I)
    (hStable : ∀ x : JH,
      AEStronglyMeasurable[p4Q2CR_actualPairHaarOffCoordinateSigma H N j]
        ((P i (P j x) : JH) : Joint → ℝ)
        muPair)
    (x : JH) :
    P i (P j x) = P j (P i x) := by
  apply p4Q2CT_symmetricProjections_commute_of_fixedInvariant
    (P i) (P j)
    (p4Q2CR_actualPairHaarCoordinateProjection_symmetric H N i)
    (p4Q2CR_actualPairHaarCoordinateProjection_symmetric H N j)
    (p4Q2CR_actualPairHaarCoordinateProjection_idempotent H N j)
  · intro y
    exact (p4Q2CR_actualPairHaarCoordinateProjection_fixed_iff
      H N j (P i (P j y))).2 (hStable y)
  · exact x

/-- Pairwise directed retention alone is enough for actual CQ
finite-coordinate Haar tensorization, with no independent commutation
hypothesis in the theorem statement. -/
theorem p4Q2CT_actualPairHaar_tensorization_of_retainedMeasurability
    (hStable : ∀ i j : I, ∀ x : JH,
      AEStronglyMeasurable[p4Q2CR_actualPairHaarOffCoordinateSigma H N j]
        ((P i (P j x) : JH) : Joint → ℝ)
        muPair)
    (x : JH) :
    ‖x - p4Q2CQ_projectionSweep P
      (p4Q2CQ_finiteCoordinates I) x‖ ^ 2 ≤
      ∑ i : I, ‖x - P i x‖ ^ 2 := by
  apply p4Q2CR_actualPairHaarProjectionSweep_tensorization_of_commuting
    H N
  · intro i j y
    exact p4Q2CT_actualPairHaarProjection_commute_of_retainedMeasurability
      H N i j (hStable i j) y
  · exact x

/-- The actual finite Haar sweep is a.e. constant when the independent
Haar sigma-algebra retention condition has been established. -/
theorem p4Q2CT_actualPairHaar_sweep_aeConst_of_retainedMeasurability
    (hStable : ∀ i j : I, ∀ x : JH,
      AEStronglyMeasurable[p4Q2CR_actualPairHaarOffCoordinateSigma H N j]
        ((P i (P j x) : JH) : Joint → ℝ)
        muPair)
    (x : JH) :
    ∃ c : ℝ,
      (p4Q2CQ_projectionSweep P (p4Q2CQ_finiteCoordinates I) x :
        Joint → ℝ) =ᵐ[muPair] fun _ => c := by
  apply p4Q2CS_actualPairHaarSweep_aeConst_of_commuting H N
  · intro i j y
    exact p4Q2CT_actualPairHaarProjection_commute_of_retainedMeasurability
      H N i j (hStable i j) y
  · exact x

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
