import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteCoreDensity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialResidualKernel
import Mathlib.Tactic

/-!
# Dense bounded-core closure for twelve-spatial Poincare estimates

The genuine ground-state joint L2 carrier already has:

* a dense core of bounded strongly measurable concrete representatives;
* twelve genuine spatial conditional expectations;
* a conventional twelve-spatial residual energy whose kernel is exactly the
  intrinsic constant line.

This file isolates the purely Hilbert/topological closure step needed before
the remaining quantitative approximate-tensorization argument.

If a relative twelve-spatial Poincare estimate is proved on the bounded
concrete core with respect to any continuous linear centering operator, then
the same estimate holds on the full genuine joint L2 carrier with exactly the
same coefficient.  No density constant and no volume factor are introduced.

A second theorem records the corresponding ordinary coercive estimate on any
sector on which the chosen centering operator vanishes, in particular the
future orthogonal complement of the intrinsic constant line once its
orthogonal projection is selected.

No positive Poincare coefficient is asserted in this file.
-/

namespace MGAP4D.MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

/-- The normalized residual energy of any finite family of continuous linear
maps is a continuous scalar function of the Hilbert vector. -/
theorem continuous_groundStateJointColorNormalizedResidualEnergy
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E) :
    Continuous (groundStateJointColorNormalizedResidualEnergy P) := by
  unfold groundStateJointColorNormalizedResidualEnergy
  fun_prop

/-- The genuine conventional twelve-spatial residual energy is continuous on
the actual ground-state joint L2 carrier. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
  exact
    continuous_groundStateJointColorNormalizedResidualEnergy
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta)

/-- A relative twelve-spatial Poincare estimate on the dense bounded concrete
core extends to every vector in the genuine ground-state joint L2 carrier.

The centering map is deliberately abstract but continuous-linear.  The theorem
does not identify it with the constant-line orthogonal projection; it only
removes the quotient-representative/density obstruction from the subsequent
quantitative argument. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialRelativePoincare_of_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (kappa : ℝ)
    (center :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)
    (hcore :
      ∀ z :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta,
        z ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
              H N hN beta hbeta →
          kappa * ‖z - center z‖ ^ 2 ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
              H N hN beta hbeta z) :
    ∀ z :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta,
      kappa * ‖z - center z‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta z := by
  let core : Set
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta
  let good : Set
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :=
    {z |
      kappa * ‖z - center z‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta z}
  have hLeft :
      Continuous
        (fun z :
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta =>
          kappa * ‖z - center z‖ ^ 2) := by
    fun_prop
  have hRight :
      Continuous
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
          H N hN beta hbeta) :=
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
      H N hN beta hbeta
  have hGoodClosed : IsClosed good := by
    simpa [good] using isClosed_le hLeft hRight
  have hCoreSub : core ⊆ good := by
    intro z hz
    exact hcore z (by simpa [core] using hz)
  have hClosureSub : closure core ⊆ good :=
    closure_minimal hCoreSub hGoodClosed
  have hDense : Dense core := by
    simpa [core] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
        H N hN beta hbeta
  intro z
  have hzClosure : z ∈ closure core := by
    rw [hDense.closure_eq]
    exact Set.mem_univ z
  exact hClosureSub hzClosure

/-- Sector form of the dense-core closure theorem.

If the chosen continuous centering operator vanishes on a sector, a relative
bounded-core estimate yields the ordinary norm-coercive twelve-spatial
Poincare inequality on that sector, with no loss of coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_on_sector_of_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (kappa : ℝ)
    (center :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)
    (sector :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta → Prop)
    (hcenter :
      ∀ z :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta,
        sector z → center z = 0)
    (hcore :
      ∀ z :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta,
        z ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
              H N hN beta hbeta →
          kappa * ‖z - center z‖ ^ 2 ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
              H N hN beta hbeta z) :
    ∀ z :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta,
      sector z →
        kappa * ‖z‖ ^ 2 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
            H N hN beta hbeta z := by
  have hall :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialRelativePoincare_of_boundedConcreteCore
      H N hN beta hbeta kappa center hcore
  intro z hz
  simpa [hcenter z hz] using hall z

end

end MGAP4D.MathlibAnalytic
