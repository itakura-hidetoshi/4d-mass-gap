import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0PhysicalPlaquetteGibbsCovarianceV5_PZ37AMG
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointPlaquetteLocalDistanceLowerBound
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMH — physical coordinate separation for original beta0 SU2 Gibbs plaquettes

AMG has already certified genuine interacting fixed-beta0 SU2 Wilson Gibbs
covariance decay when the two actual four-link plaquette supports have typed
Wilson-plaquette-local path separation. This file discharges that support
hypothesis using a genuine periodic Euclidean *time-coordinate* distance.

Every actual boundary positive-link source time is within one lattice unit of
its plaquette base time; the two boundary displacements cost at most two.
One local Wilson-plaquette edge step costs at most one in cyclic source time.
Therefore a base-time distance of at least D+2 implies D-step actual physical
support separation; AMG then gives the original Gibbs bound with coefficient 64.

The unconditional exponent is the truncated base-time distance (distance - 2).
This is a projection to ONE physical coordinate, not the full four-dimensional
Euclidean distance, and does NOT imply a volume-uniform four-dimensional
covariance shell sum. The existing 24^D shell bound is too coarse at beta0:
24 * rho0 > 1. Four-dimensional polynomial shell counting and a Gauss-law
physical OS transfer bridge remain independent obstructions. Neither a
Hamiltonian gap nor a 4D continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace GroundStatePosteriorJoint

/-- Every genuine positive boundary link of a physical periodic plaquette
has source time at cyclic distance at most one from its plaquette base. -/
theorem p4Q2PZ37AMH_originalBoundaryLink_baseTimeCyclicDistance_le_one
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (e : PeriodicHypercubicEvenEdge H)
    (he : e ∈ periodicHypercubicEvenPlaquetteEdgeSupport H p) :
    periodicHypercubicEvenTimeCyclicDistance H (p.1 0) (e.1 0) ≤ 1 := by
  classical
  simp only [periodicHypercubicEvenPlaquetteEdgeSupport,
    Finset.mem_image, Finset.mem_univ, true_and] at he
  rcases he with ⟨k, rfl⟩
  rcases periodicHypercubicEvenBoundaryStep_edge_sourceTime_eq_base_or_add_one
      H p k with hbase | hnext
  · rw [hbase]
    simp
  · rw [hnext]
    exact (periodicHypercubicEvenTimeCyclicDistance_add_one_right H (p.1 0)).le

/-- The base-time distance of two ACTUAL plaquettes is at most the cyclic
source-time distance of any selected physical boundary-link pair plus two.
The two units are geometric endpoint costs, not a probabilistic estimate. -/
theorem p4Q2PZ37AMH_originalPlaquetteBaseTimeDistance_le_two_add_linkDistance
    (H : ℕ) (p q : PeriodicHypercubicEvenPlaquette H)
    (e f : PeriodicHypercubicEvenEdge H)
    (he : e ∈ periodicHypercubicEvenPlaquetteEdgeSupport H p)
    (hf : f ∈ periodicHypercubicEvenPlaquetteEdgeSupport H q) :
    periodicHypercubicEvenTimeCyclicDistance H (p.1 0) (q.1 0) ≤
      2 + periodicHypercubicEvenSourceTimeCyclicDistance H e f := by
  have hLeft :
      periodicHypercubicEvenTimeCyclicDistance H (p.1 0) (e.1 0) ≤ 1 :=
    p4Q2PZ37AMH_originalBoundaryLink_baseTimeCyclicDistance_le_one H p e he
  have hRight :
      periodicHypercubicEvenTimeCyclicDistance H (f.1 0) (q.1 0) ≤ 1 := by
    rw [periodicHypercubicEvenTimeCyclicDistance_comm]
    exact p4Q2PZ37AMH_originalBoundaryLink_baseTimeCyclicDistance_le_one H q f hf
  have hTriangleLeft :=
    periodicHypercubicEvenTimeCyclicDistance_triangle H
      (p.1 0) (e.1 0) (q.1 0)
  have hTriangleRight :=
    periodicHypercubicEvenTimeCyclicDistance_triangle H
      (e.1 0) (f.1 0) (q.1 0)
  change periodicHypercubicEvenTimeCyclicDistance H (p.1 0) (q.1 0) ≤
    2 + periodicHypercubicEvenTimeCyclicDistance H (e.1 0) (f.1 0)
  omega

/-- A *concrete physical* plaquette base-time gap D+2 proves the exact
Wilson-plaquette-local support-separation predicate consumed by AMG.
No separation of shared-link adjacent plaquettes is inserted. -/
theorem p4Q2PZ37AMH_originalPhysicalPlaquetteSupports_separated_of_baseTime
    (H D : ℕ) (p q : PeriodicHypercubicEvenPlaquette H)
    (hBase : D + 2 ≤
      periodicHypercubicEvenTimeCyclicDistance H (q.1 0) (p.1 0)) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D
      (periodicHypercubicEvenPlaquetteEdgeSupport H q)
      (periodicHypercubicEvenPlaquetteEdgeSupport H p) := by
  intro d hd e he f hf hpath
  have hBaseLink :=
    p4Q2PZ37AMH_originalPlaquetteBaseTimeDistance_le_two_add_linkDistance
      H q p e f he hf
  have hPathBound :=
    periodicHypercubicEvenPlaquetteLocalPath_sourceTimeCyclicDistance_le_length
      H d hpath
  omega

/-- Actual SU2 Wilson Gibbs connected physical-character covariance decays
from an explicit periodic physical base-time separation bound. -/
theorem p4Q2PZ37AMH_originalFixedBeta0GibbsCovariance_abs_le_of_baseTime
    (H D : ℕ) (hH : 0 < H)
    (p q : PeriodicHypercubicEvenPlaquette H)
    (hBase : D + 2 ≤
      periodicHypercubicEvenTimeCyclicDistance H (q.1 0) (p.1 0)) :
    let F := p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p
    let O := p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q
    |(p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
      (fun A => F A) (fun A => O A)| ≤
      64 * ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant
          p4Q2PZ37ADC_fixedCoupling) ^ D /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant
          p4Q2PZ37ADC_fixedCoupling)) := by
  dsimp only
  exact
    p4Q2PZ37AMG_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_abs_le_explicit
      H D hH p q
      (p4Q2PZ37AMH_originalPhysicalPlaquetteSupports_separated_of_baseTime
        H D p q hBase)

/-- For EVERY physical plaquette pair, the positive-path separation exponent
is at least the truncated cyclic physical base-time distance minus two.
For nearby plaquettes this is zero, preserving the shared-link obstruction. -/
theorem p4Q2PZ37AMH_originalPhysicalPlaquetteSupports_separated_by_baseTimeSubTwo
    (H : ℕ) (p q : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H
      (periodicHypercubicEvenTimeCyclicDistance H (q.1 0) (p.1 0) - 2)
      (periodicHypercubicEvenPlaquetteEdgeSupport H q)
      (periodicHypercubicEvenPlaquetteEdgeSupport H p) := by
  by_cases hBase : 2 ≤
      periodicHypercubicEvenTimeCyclicDistance H (q.1 0) (p.1 0)
  · apply p4Q2PZ37AMH_originalPhysicalPlaquetteSupports_separated_of_baseTime
      H _ p q
    omega
  · have hZero :
        periodicHypercubicEvenTimeCyclicDistance H (q.1 0) (p.1 0) - 2 = 0 := by
      omega
    rw [hZero]
    intro d hd
    omega

/-- Unconditional actual SU2 Wilson finite Gibbs character covariance bound
with a fully concrete periodic physical time-coordinate distance exponent.
A one-coordinate decay theorem is NOT a full 4D distance/shell theorem. -/
theorem p4Q2PZ37AMH_originalFixedBeta0GibbsCovariance_abs_le_baseTimeSubTwo
    (H : ℕ) (hH : 0 < H)
    (p q : PeriodicHypercubicEvenPlaquette H) :
    let F := p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H p
    let O := p4Q2PZ37AMG_originalPhysicalPlaquetteCharacterBCF H q
    |(p4Q2PZ37AMG_originalFixedBeta0System H).gibbsCovarianceReal
      (fun A => F A) (fun A => O A)| ≤
      64 * ((18 * periodicHypercubicSpecialUnitaryActiveTVMajorant
          p4Q2PZ37ADC_fixedCoupling) ^
          (periodicHypercubicEvenTimeCyclicDistance H (q.1 0) (p.1 0) - 2) /
        (1 - 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant
          p4Q2PZ37ADC_fixedCoupling)) := by
  dsimp only
  exact
    p4Q2PZ37AMG_originalFixedBeta0PhysicalPlaquetteGibbsCovariance_abs_le_explicit
      H _ hH p q
      (p4Q2PZ37AMH_originalPhysicalPlaquetteSupports_separated_by_baseTimeSubTwo
        H p q)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMH_originalBoundaryLink_baseTimeCyclicDistance_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMH_originalPlaquetteBaseTimeDistance_le_two_add_linkDistance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMH_originalPhysicalPlaquetteSupports_separated_of_baseTime
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMH_originalFixedBeta0GibbsCovariance_abs_le_of_baseTime
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMH_originalPhysicalPlaquetteSupports_separated_by_baseTimeSubTwo
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMH_originalFixedBeta0GibbsCovariance_abs_le_baseTimeSubTwo
