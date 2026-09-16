import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRemoteSlabCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For a background link away from the distinguished local-factor target and
away from the resampled fiber's spatial plaquette neighborhood, the literal C5
reference weight has exactly the same four-point multiplicative distortion as
the canonical continuous vacuum.

The target-local Boltzmann factor cancels because the background update is off
target.  The raw symmetric one-slab kernel cancels by geometric
noninteraction.  No locality or decay property is imposed on the canonical
vacuum; this theorem deliberately isolates that remaining obstruction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_remote_background_crossRatio_isolates_vacuum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hFiberBackground : fiber ≠ backgroundFiber)
    (hBackgroundTarget : backgroundFiber ≠ target)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H backgroundFiber fiber)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (u v g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let Cug := Function.update (Function.update A fiber u) backgroundFiber g
    let Cvh := Function.update (Function.update A fiber v) backgroundFiber h
    let Cuh := Function.update (Function.update A fiber u) backgroundFiber h
    let Cvg := Function.update (Function.update A fiber v) backgroundFiber g
    let Omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cug *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cvh) *
      (Omega Cuh * Omega Cvg) =
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cuh *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ Cvg) *
      (Omega Cug * Omega Cvh) := by
  dsimp only
  let Au : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A fiber u
  let Av : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A fiber v
  let Cug : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update Au backgroundFiber g
  let Cvh : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update Av backgroundFiber h
  let Cuh : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update Au backgroundFiber h
  let Cvg : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update Av backgroundFiber g
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let Local := fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta X B target g₂
  let slab := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let Br : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B source k
  have hLocalUg : Local Cug = Local Au := by
    simpa [Local, Cug] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
        H N beta Au B target backgroundFiber g g₂ hBackgroundTarget
  have hLocalUh : Local Cuh = Local Au := by
    simpa [Local, Cuh] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
        H N beta Au B target backgroundFiber h g₂ hBackgroundTarget
  have hLocalVh : Local Cvh = Local Av := by
    simpa [Local, Cvh] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
        H N beta Av B target backgroundFiber h g₂ hBackgroundTarget
  have hLocalVg : Local Cvg = Local Av := by
    simpa [Local, Cvg] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
        H N beta Av B target backgroundFiber g g₂ hBackgroundTarget
  have hSlabRight :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_remote_background_crossRatio_eq
      H N beta Br A fiber backgroundFiber u v g h hFiberBackground hNoShare
  have hSymUg : slab Cug Br = slab Br Cug := by
    simpa [slab] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
        H N hN beta hbeta Cug Br
  have hSymVh : slab Cvh Br = slab Br Cvh := by
    simpa [slab] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
        H N hN beta hbeta Cvh Br
  have hSymUh : slab Cuh Br = slab Br Cuh := by
    simpa [slab] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
        H N hN beta hbeta Cuh Br
  have hSymVg : slab Cvg Br = slab Br Cvg := by
    simpa [slab] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
        H N hN beta hbeta Cvg Br
  have hSlab :
      slab Cug Br * slab Cvh Br = slab Cuh Br * slab Cvg Br := by
    calc
      slab Cug Br * slab Cvh Br = slab Br Cug * slab Br Cvh := by
        rw [hSymUg, hSymVh]
      _ = slab Br Cuh * slab Br Cvg := by
        simpa [slab, Br, Cug, Cvh, Cuh, Cvg, Au, Av] using hSlabRight
      _ = slab Cuh Br * slab Cvg Br := by
        rw [← hSymUh, ← hSymVg]
  change
    (((Omega Cug * Local Cug) * slab Cug Br) *
        ((Omega Cvh * Local Cvh) * slab Cvh Br)) *
      (Omega Cuh * Omega Cvg) =
    (((Omega Cuh * Local Cuh) * slab Cuh Br) *
        ((Omega Cvg * Local Cvg) * slab Cvg Br)) *
      (Omega Cug * Omega Cvh)
  rw [hLocalUg, hLocalVh, hLocalUh, hLocalVg]
  calc
    ((((Omega Cug * Local Au) * slab Cug Br) *
        ((Omega Cvh * Local Av) * slab Cvh Br)) *
      (Omega Cuh * Omega Cvg)) =
      (Omega Cug * Omega Cvh * Omega Cuh * Omega Cvg *
        Local Au * Local Av) *
        (slab Cug Br * slab Cvh Br) := by ring
    _ = (Omega Cug * Omega Cvh * Omega Cuh * Omega Cvg *
        Local Au * Local Av) *
        (slab Cuh Br * slab Cvg Br) := by rw [hSlab]
    _ = ((((Omega Cuh * Local Au) * slab Cuh Br) *
        ((Omega Cvg * Local Av) * slab Cvg Br)) *
      (Omega Cug * Omega Cvh)) := by ring

end

end MathlibAnalytic
end MGAP4D