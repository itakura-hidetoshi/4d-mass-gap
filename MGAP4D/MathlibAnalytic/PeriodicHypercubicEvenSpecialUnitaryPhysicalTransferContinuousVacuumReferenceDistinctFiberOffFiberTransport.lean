import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryHeatBathDistinctFiberTransportCriterion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceDistinctFiberOffFiberTransportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Changing one left-background spatial link changes the literal C5 reference
weight by at most the volume-independent factor `exp (32 * beta)`.

The three physical pieces are kept separate: the canonical continuous vacuum
costs `exp (8 * beta)`, the target-local factor costs `exp (16 * beta)` by its
uniform two-sided bounds, and the symmetric one-slab kernel costs
`exp (8 * beta)` after moving the changed left boundary to the right by kernel
symmetry. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂
          (Function.update A backgroundFiber g) ≤
        Real.exp (32 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B target source k g₂
            (Function.update A backgroundFiber h) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂
          (Function.update A backgroundFiber h) ≤
        Real.exp (32 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B target source k g₂
            (Function.update A backgroundFiber g) := by
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let Local := fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta X B target g₂
  let slab := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let Br : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update B source k
  have hExp :
      (Real.exp (8 * beta) * Real.exp (16 * beta)) * Real.exp (8 * beta) =
        Real.exp (32 * beta) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hdir : ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ (Function.update A backgroundFiber g) ≤
        Real.exp (32 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B target source k g₂ (Function.update A backgroundFiber h) := by
    intro g h
    let Ag : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
      Function.update A backgroundFiber g
    let Ah : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
      Function.update A backgroundFiber h
    have hOmega : Omega Ag ≤ Real.exp (8 * beta) * Omega Ah := by
      simpa [Omega, Ag, Ah,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
          H N hN beta hbeta A backgroundFiber g h
    have hLocalUpper : Local Ag ≤ Real.exp (8 * beta) := by
      simpa [Local, Ag] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
          H N hN beta hbeta Ag B target g₂
    have hLocalLower : Real.exp (-8 * beta) ≤ Local Ah := by
      simpa [Local, Ah] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
          H N hN beta hbeta Ah B target g₂
    have hLocal : Local Ag ≤ Real.exp (16 * beta) * Local Ah := by
      calc
        Local Ag ≤ Real.exp (8 * beta) := hLocalUpper
        _ = Real.exp (16 * beta) * Real.exp (-8 * beta) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (16 * beta) * Local Ah :=
          mul_le_mul_of_nonneg_left hLocalLower (Real.exp_pos _).le
    have hSlabSymm : slab Br Ah = slab Ah Br := by
      simpa [slab] using
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
          H N hN beta hbeta Ah Br).symm
    have hSlab : slab Ag Br ≤ Real.exp (8 * beta) * slab Ah Br := by
      calc
        slab Ag Br = slab Br Ag := by
          simpa [slab] using
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
              H N hN beta hbeta Ag Br
        _ ≤ Real.exp (8 * beta) * slab Br Ah := by
          simpa [slab, Ag, Ah,
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
              H N hN beta hbeta Br A backgroundFiber g h
        _ = Real.exp (8 * beta) * slab Ah Br := by rw [hSlabSymm]
    have hOmegaAhNonneg : 0 ≤ Omega Ah :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta Ah).le
    have hLocalAgNonneg : 0 ≤ Local Ag := by
      exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta Ag B target g₂).le
    have hLocalAhNonneg : 0 ≤ Local Ah := by
      exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta Ah B target g₂).le
    have hSlabAgNonneg : 0 ≤ slab Ag Br := by
      exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta Ag Br).le
    have hOmegaUpperNonneg : 0 ≤ Real.exp (8 * beta) * Omega Ah :=
      mul_nonneg (Real.exp_pos _).le hOmegaAhNonneg
    have hPair :
        Omega Ag * Local Ag ≤
          (Real.exp (8 * beta) * Omega Ah) *
            (Real.exp (16 * beta) * Local Ah) :=
      mul_le_mul hOmega hLocal hLocalAgNonneg hOmegaUpperNonneg
    have hPairUpperNonneg :
        0 ≤ (Real.exp (8 * beta) * Omega Ah) *
          (Real.exp (16 * beta) * Local Ah) :=
      mul_nonneg hOmegaUpperNonneg
        (mul_nonneg (Real.exp_pos _).le hLocalAhNonneg)
    have hAll :
        (Omega Ag * Local Ag) * slab Ag Br ≤
          ((Real.exp (8 * beta) * Omega Ah) *
            (Real.exp (16 * beta) * Local Ah)) *
              (Real.exp (8 * beta) * slab Ah Br) :=
      mul_le_mul hPair hSlab hSlabAgNonneg hPairUpperNonneg
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    change (Omega Ag * Local Ag) * slab Ag Br ≤
      Real.exp (32 * beta) * ((Omega Ah * Local Ah) * slab Ah Br)
    calc
      (Omega Ag * Local Ag) * slab Ag Br ≤
          ((Real.exp (8 * beta) * Omega Ah) *
            (Real.exp (16 * beta) * Local Ah)) *
              (Real.exp (8 * beta) * slab Ah Br) := hAll
      _ = ((Real.exp (8 * beta) * Real.exp (16 * beta)) * Real.exp (8 * beta)) *
          ((Omega Ah * Local Ah) * slab Ah Br) := by ring
      _ = Real.exp (32 * beta) * ((Omega Ah * Local Ah) * slab Ah Br) := by
        rw [hExp]
  exact ⟨hdir g h, hdir h g⟩

end

end MathlibAnalytic
end MGAP4D
