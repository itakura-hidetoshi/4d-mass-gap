import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkRegularConditionalDistribution
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFullKernelSectionBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

local instance remoteKernelSectionOneLinkRcdSpecialUnitaryIsTopologicalGroup
    (N : Nat) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance remoteKernelSectionOneLinkRcdSpecialUnitaryCompactSpace
    (N : Nat) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupCompactSpace N

local instance remoteKernelSectionOneLinkRcdAmbientMatrixSecondCountableTopology
    (N : Nat) : SecondCountableTopology (Matrix (Fin N) (Fin N) Complex) :=
  specialUnitaryAmbientMatrixSecondCountableTopology N

local instance remoteKernelSectionOneLinkRcdAmbientMatrixIsCompletelyMetrizableSpace
    (N : Nat) :
    TopologicalSpace.IsCompletelyMetrizableSpace (Matrix (Fin N) (Fin N) Complex) := by
  change TopologicalSpace.IsCompletelyMetrizableSpace (Fin N -> Fin N -> Complex)
  infer_instance

local instance remoteKernelSectionOneLinkRcdAmbientMatrixPolishSpace
    (N : Nat) : PolishSpace (Matrix (Fin N) (Fin N) Complex) := by
  infer_instance

local instance remoteKernelSectionOneLinkRcdSpecialUnitaryPolishSpace
    (N : Nat) : PolishSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  (specialUnitaryGroup_isClosed N).polishSpace

local instance remoteKernelSectionOneLinkRcdSpecialUnitarySecondCountableTopology
    (N : Nat) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupSecondCountableTopology N

local instance remoteKernelSectionOneLinkRcdSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

local instance remoteKernelSectionOneLinkRcdSpecialUnitaryBorelSpace
    (N : Nat) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupBorelSpace N

local instance remoteKernelSectionOneLinkRcdSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Outside the target/source interaction neighborhood, the already-constructed
reference one-link heat-bath kernel is an actual regular conditional
distribution for the fixed-right ground-state kernel-section law obtained by
the source update followed by the target update.

This is only a change of the ambient probability-measure presentation using the
exact full-law identity. No Gibbs identification or decay estimate is added. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_ae_eq_kernelSection_condExpKernel_of_remote
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
    (k g2 : Matrix.specialUnitaryGroup (Fin N) Complex) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
        H N hN beta hbeta B target source fiber k g2 =ᵐ[
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)).trim
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace_le H N fiber)]
      ProbabilityTheory.condExpKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber) := by
  have hMeasure :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
      H N hN beta hbeta B hne hNoShare k g2
  have hRcd :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_ae_eq_condExpKernel
      H N hN beta hbeta B target source fiber k g2
  rw [hMeasure] at hRcd
  exact hRcd

/-- The same remote full-law identification transports the exact one-link
conditional-expectation representative to the fixed-right ground-state
kernel-section law for every integrable real observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_ae_eq_kernelSection_condExp_of_remote
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
    (hf : Integrable f
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2))) :
    (fun A =>
      ∫ C, f C ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel
          H N hN beta hbeta B target source fiber k g2 A) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g2)]
      MeasureTheory.condExp
        (periodicHypercubicEvenSpecialUnitarySpatialSliceOffFiberMeasurableSpace H N fiber)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g2))
        f := by
  have hMeasure :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_eq_kernelSection_source_then_target_of_remote
      H N hN beta hbeta B hne hNoShare k g2
  have hfReference :
      Integrable f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g2) := by
    rw [hMeasure]
    exact hf
  have hCond :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkOffFiberHeatBathKernel_ae_eq_condExp
      H N hN beta hbeta B target source fiber k g2 f hfReference
  rw [hMeasure] at hCond
  exact hCond

end

end MathlibAnalytic
end MGAP4D
