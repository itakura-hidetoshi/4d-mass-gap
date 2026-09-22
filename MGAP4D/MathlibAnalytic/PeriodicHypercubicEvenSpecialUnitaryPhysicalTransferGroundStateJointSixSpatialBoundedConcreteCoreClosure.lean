import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteCoreDensity
import Mathlib.Tactic

/-!
# Six-spatial bounded-core closure on the genuine ground-state joint L2 carrier

The bounded concrete representatives used by the sharp one-link variance
theorems are already dense in the genuine Wilson ground-state joint L2 space.

This file isolates the purely topological closure step for the six genuine
right-boundary spatial conditional expectations. If a quantitative relative
Poincare estimate is proved on that bounded concrete core, then it extends to
the entire joint L2 carrier with exactly the same coefficient.

No positive Poincare coefficient is asserted here. In particular, no
variation contraction is promoted directly to an L2 Rayleigh bound.
-/

namespace MGAP4D.MathlibAnalytic

open Set
open scoped BigOperators

noncomputable section

/-- Six-spatial normalized residual energy on the full genuine joint L2
carrier. This is the same finite one-sixth projection-residual energy that is
evaluated on right-boundary lifts in the existing six-spatial transfer-gap
receiver, before restricting its argument to such a lift. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) : ℝ :=
  groundStateJointColorNormalizedResidualEnergy
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
      H N hN beta hbeta) z

/-- The normalized residual energy of a finite family of continuous linear
maps is continuous in the Hilbert vector. -/
theorem continuous_groundStateJointColorNormalizedResidualEnergy
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E) :
    Continuous (groundStateJointColorNormalizedResidualEnergy P) := by
  unfold groundStateJointColorNormalizedResidualEnergy
  fun_prop

/-- The genuine six-spatial joint residual energy is continuous. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
  exact
    continuous_groundStateJointColorNormalizedResidualEnergy
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        H N hN beta hbeta)

/-- Any relative six-spatial Poincare estimate established on the already
proved dense bounded-concrete core extends to the entire genuine joint L2
carrier without loss in the coefficient.

The continuous linear map center is deliberately abstract. This separates the
Hilbert-space closure issue from the remaining analytic task of choosing and
controlling the correct common-fixed-sector projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialRelativePoincare_of_boundedConcreteCore
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
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
              H N hN beta hbeta z) :
    ∀ z :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta,
      kappa * ‖z - center z‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
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
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
          H N hN beta hbeta) :=
    continuous_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
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

/-- Sector form of the bounded-core closure theorem.

When the chosen continuous centering operator vanishes on a sector, the
relative core estimate yields ordinary norm coercivity on that sector with no
loss of constant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialPoincare_on_sector_of_boundedConcreteCore
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
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
              H N hN beta hbeta z) :
    ∀ z :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta,
      sector z →
        kappa * ‖z‖ ^ 2 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
            H N hN beta hbeta z := by
  have hall :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialRelativePoincare_of_boundedConcreteCore
      H N hN beta hbeta kappa center hcore
  intro z hz
  simpa [hcenter z hz] using hall z

end

end MGAP4D.MathlibAnalytic
