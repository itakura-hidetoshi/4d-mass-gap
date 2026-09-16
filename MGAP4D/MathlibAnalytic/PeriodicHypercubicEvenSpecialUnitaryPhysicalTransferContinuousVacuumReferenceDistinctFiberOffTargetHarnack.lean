import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceDistinctFiberOffTargetHarnackSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Updating a left-background link away from the distinguished right target
leaves the exact target-local Boltzmann factor unchanged.  The left-boundary
configuration enters that factor only through its value at `target`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (g g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hBackgroundTarget : backgroundFiber ≠ target) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta (Function.update A backgroundFiber g) B target g₂ =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g₂ := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor,
    hBackgroundTarget, Ne.symm hBackgroundTarget]

/-- Away from the distinguished right target, the `exp (16 * beta)` local-factor
cost in the previous `exp (32 * beta)` raw Harnack theorem is absent exactly.
Only the canonical continuous-vacuum comparison and the symmetric one-slab
kernel comparison remain, giving `exp (16 * beta)` in either direction.

This is a support sharpening of the literal reference weight.  It does not
assert that the canonical vacuum itself has finite geometric support. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack_off_target
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source backgroundFiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (hBackgroundTarget : backgroundFiber ≠ target)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂
          (Function.update A backgroundFiber g) ≤
        Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
            H N hN beta hbeta B target source k g₂
            (Function.update A backgroundFiber h) ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂
          (Function.update A backgroundFiber h) ≤
        Real.exp (16 * beta) *
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
      Real.exp (8 * beta) * Real.exp (8 * beta) = Real.exp (16 * beta) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hdir : ∀ g h : Matrix.specialUnitaryGroup (Fin N) ℂ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
          H N hN beta hbeta B target source k g₂ (Function.update A backgroundFiber g) ≤
        Real.exp (16 * beta) *
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
    have hLocal : Local Ag = Local Ah := by
      calc
        Local Ag = Local A := by
          simpa [Local, Ag] using
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
              H N beta A B target backgroundFiber g g₂ hBackgroundTarget
        _ = Local Ah := by
          symm
          simpa [Local, Ah] using
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_left_of_ne
              H N beta A B target backgroundFiber h g₂ hBackgroundTarget
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
          (Real.exp (8 * beta) * Omega Ah) * Local Ah := by
      rw [hLocal]
      exact mul_le_mul_of_nonneg_right hOmega hLocalAhNonneg
    have hPairUpperNonneg :
        0 ≤ (Real.exp (8 * beta) * Omega Ah) * Local Ah :=
      mul_nonneg hOmegaUpperNonneg hLocalAhNonneg
    have hAll :
        (Omega Ag * Local Ag) * slab Ag Br ≤
          ((Real.exp (8 * beta) * Omega Ah) * Local Ah) *
            (Real.exp (8 * beta) * slab Ah Br) :=
      mul_le_mul hPair hSlab hSlabAgNonneg hPairUpperNonneg
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    change (Omega Ag * Local Ag) * slab Ag Br ≤
      Real.exp (16 * beta) * ((Omega Ah * Local Ah) * slab Ah Br)
    calc
      (Omega Ag * Local Ag) * slab Ag Br ≤
          ((Real.exp (8 * beta) * Omega Ah) * Local Ah) *
            (Real.exp (8 * beta) * slab Ah Br) := hAll
      _ = (Real.exp (8 * beta) * Real.exp (8 * beta)) *
          ((Omega Ah * Local Ah) * slab Ah Br) := by ring
      _ = Real.exp (16 * beta) * ((Omega Ah * Local Ah) * slab Ah Br) := by
        rw [hExp]
  exact ⟨hdir g h, hdir h g⟩

end

end MathlibAnalytic
end MGAP4D
