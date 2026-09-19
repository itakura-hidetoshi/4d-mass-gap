import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanCovarianceDirichlet
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance remoteKernelSectionRestrictedRandomScanIterateSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionRestrictedRandomScanIterateSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionRestrictedRandomScanIterateKernelSectionProbabilityMeasure
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
    H N hN beta hbeta C

/-- One actual physical restricted random-scan step preserves strong
measurability.  This is the finite uniform average of the already-proved
strongly measurable singleton deterministic schedules. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_stronglyMeasurable
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : StronglyMeasurable F) :
    StronglyMeasurable
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
          H N hN beta hbeta B target source g2 k A F) := by
  classical
  let P :
      PeriodicHypercubicEvenSpatialSliceLink H ->
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
    fun fiber A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation
        H N hN beta hbeta B target source g2 [fiber] k A F
  have hP :
      forall fiber : PeriodicHypercubicEvenSpatialSliceLink H,
        StronglyMeasurable (P fiber) := by
    intro fiber
    dsimp [P]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberDeterministicScheduleExpectation_stronglyMeasurable
        H N hN beta hbeta B target source g2 k [fiber] F hF
  have hSum :
      StronglyMeasurable
        (fun A => ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H, P fiber A) := by
    exact
      Finset.stronglyMeasurable_fun_sum Finset.univ
        (fun fiber _ => hP fiber)
  have hScaled :=
    hSum.const_mul
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : Real)⁻¹
  simpa [
    P,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation] using
    hScaled

/-- Actual physical restricted random-scan iteration.  The initial observable is
iteration zero and every successor applies exactly one physical restricted
random-scan step. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real) :
    Nat ->
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real
  | 0 => F
  | n + 1 =>
      fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
          H N hN beta hbeta B target source g2 k A
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g2 k F n)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_zero
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g2 k F 0 = F := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (n : Nat) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
        H N hN beta hbeta B target source g2 k F (n + 1) =
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation
          H N hN beta hbeta B target source g2 k A
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g2 k F n)) := by
  rfl

/-- Every finite physical restricted random-scan iterate remains strongly
measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : StronglyMeasurable F) :
    forall n : Nat,
      StronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k F n) := by
  intro n
  induction n with
  | zero =>
      simpa using hF
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_stronglyMeasurable
          H N hN beta hbeta B target source g2 k
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g2 k F n)
          ih

/-- Every finite physical restricted random-scan iterate preserves L2 under the
fixed remote kernel-section probability law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScanExpectationIterate_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    forall n : Nat,
      MemLp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k F n)
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2)) := by
  intro n
  induction n with
  | zero =>
      simpa using hF
  | succ n ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionRestrictedRandomScanExpectation_memLp_two
          H N hN beta hbeta B hne hNoShare k g2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
            H N hN beta hbeta B target source g2 k F n)
          ih

/-- The physical restricted random-scan orbit is dominated, step by step, by
the exact restricted tagged-carrier variation iterate.  Only physical left
fibers are varied; represented right-source coordinates remain carrier state
coordinates and are not update targets. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g2 k : Matrix.specialUnitaryGroup (Fin N) Complex)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hF : StronglyMeasurable F)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H -> Real)
    (hVariationNonneg : forall e, 0 <= variation e)
    (hVariation :
      forall (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
        |F (Function.update C e u) - F (Function.update C e v)| <= variation e) :
    forall (n : Nat)
      (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (u v : Matrix.specialUnitaryGroup (Fin N) Complex),
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k F n (Function.update A e u) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k F n (Function.update A e v)| <=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta variation n (Sum.inl e) := by
  intro n
  induction n with
  | zero =>
      intro e A u v
      simpa using hVariation e A u v
  | succ n ih =>
      intro e A u v
      let G : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
          H N hN beta hbeta B target source g2 k F n
      let profile :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) -> Real :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta variation n
      have hG : StronglyMeasurable G := by
        dsimp [G]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source g2 k F hF n
      have hProfileNonneg : forall x, 0 <= profile x := by
        intro x
        dsimp [profile]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
            H beta hbeta variation hVariationNonneg n x
      have hGVariation :
          forall (background : PeriodicHypercubicEvenSpatialSliceLink H)
            (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
            (a b : Matrix.specialUnitaryGroup (Fin N) Complex),
            |G (Function.update C background a) -
              G (Function.update C background b)| <=
                profile (Sum.inl background) := by
        intro background C a b
        simpa [G, profile] using ih background C a b
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectation_fiberVariation_le
          H N hN beta hbeta B target source g2 k G hG profile
          hProfileNonneg hGVariation e A u v
      simpa [
        G,
        profile,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_succ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_succ] using
        hStep

end

end MathlibAnalytic
end MGAP4D
