import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjectionIdempotent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionOneLinkProjectionL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionOneLinkProjectionFluctuationAnnihilationSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionOneLinkProjectionFluctuationAnnihilationSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remoteKernelSectionOneLinkProjectionFluctuationAnnihilationKernelSectionProbabilityMeasure
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

/-- The actual remote kernel-section one-link projection respects subtraction
almost everywhere on square-integrable observables.  This is transported from
conditional-expectation subtraction through the exact a.e. projection
identification. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_sub_ae_of_memLp_two
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
    (f g : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real)
    (hf : MemLp f 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)))
    (hg : MemLp g 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta B target source fiber k g2 (f - g) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 g := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hfInt : Integrable f mu :=
    memLp_one_iff_integrable.1 (hf.mono_exponent one_le_two)
  have hgInt : Integrable g mu :=
    memLp_one_iff_integrable.1 (hg.mono_exponent one_le_two)
  have hfgInt : Integrable (f - g) mu :=
    hfInt.sub hgInt
  have hSubProjection :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_ae_eq_condExp
      H N hN beta hbeta B hne hNoShare fiber k g2 (f - g) hfgInt
  have hfProjection :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_ae_eq_condExp
      H N hN beta hbeta B hne hNoShare fiber k g2 f hfInt
  have hgProjection :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_ae_eq_condExp
      H N hN beta hbeta B hne hNoShare fiber k g2 g hgInt
  have hCondSub :
      MeasureTheory.condExp
          (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
          mu (f - g) =ᵐ[mu]
        MeasureTheory.condExp
            (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
            mu f -
          MeasureTheory.condExp
            (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
            mu g := by
    exact MeasureTheory.condExp_sub hfInt hgInt
      (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
  exact
    hSubProjection.trans
      (hCondSub.trans
        (hfProjection.symm.sub hgProjection.symm))

/-- The actual remote one-link projection annihilates its complementary
fluctuation almost everywhere: P(Q f) = 0. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_fluctuation_ae_eq_zero_of_memLp_two
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
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta B target source fiber k g2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation
          H N hN beta hbeta B target source fiber k g2 f) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)]
      (0 : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g2)
  have hPf :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 f hf
  have hSub :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_sub_ae_of_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2
      f
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
        H N hN beta hbeta B target source fiber k g2 f)
      hf hPf
  have hIdem :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection_idempotent_ae_of_memLp_two
      H N hN beta hbeta B hne hNoShare fiber k g2 f hf
  have hZero :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2 f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
          H N hN beta hbeta B target source fiber k g2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkProjection
            H N hN beta hbeta B target source fiber k g2 f) =ᵐ[mu]
        (0 : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N -> Real) := by
    filter_upwards [hIdem] with A hA
    simp only [Pi.sub_apply, Pi.zero_apply, hA, sub_self]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation] using
    hSub.trans hZero

end

end MathlibAnalytic
end MGAP4D
