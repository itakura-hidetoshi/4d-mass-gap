import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjection
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionOneLinkProjectionL2SpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionOneLinkProjectionL2SpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionOneLinkProjectionL2KernelSectionProbabilityMeasure
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

/-- The actual remote kernel-section one-link conditional projection preserves
square integrability.  This is transported from the pinned mathlib L2
conditional-expectation theorem through the exact almost-everywhere projection
identity; no Gibbs-law identification is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hf : MemLp f 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta B target source fiber k g2 f)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hfInt : Integrable f mu :=
    memLp_one_iff_integrable.1 (hf.mono_exponent one_le_two)
  have hAE :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_ae_eq_condExp
      H N hN beta hbeta B hne hNoShare fiber k g2 f hfInt
  have hCond : MemLp
      (MeasureTheory.condExp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
        mu f)
      2 mu := by
    simpa using (hf.condExp
      (m := periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber))
  apply hCond.congr_norm (hCond.aestronglyMeasurable.congr hAE.symm)
  filter_upwards [hAE] with A hA
  rw [hA]

/-- Consequently the one-link fluctuation f - P_f is square integrable whenever
f is square integrable under the actual remote kernel-section law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_memLp_two
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hf : MemLp f 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
        H N hN beta hbeta B target source fiber k g2 f)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)) := by
  have hProjection :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 f hf
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation] using
    hf.sub hProjection

end

end MathlibAnalytic
end MGAP4D
