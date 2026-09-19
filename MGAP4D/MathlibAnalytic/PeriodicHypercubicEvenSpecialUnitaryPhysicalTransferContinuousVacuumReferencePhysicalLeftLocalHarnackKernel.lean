import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
import Mathlib.Tactic

/-!
# Local Harnack kernel inside the physical continuous-vacuum envelope

The actual physical left-background influence envelope already splits exactly
into two pieces:

* an active-neighbor local term with the volume-independent Harnack
  coefficient;
* the source-aligned remote physical vacuum residual.

This file promotes the first piece to its own finite nonnegative influence
kernel.  The separation is exact, not an approximation.  The local kernel has
at most eighteen nonzero entries in every source column.

No claim is made here that the remote residual vanishes, decays, or is
dominated by the local kernel.  This is the carrier needed for a later
local-Green-plus-remote-perturbation argument.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance physicalLeftLocalHarnackKernelSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalLeftLocalHarnackKernelSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The genuinely local part of the actual physical left influence envelope:
one Harnack coefficient on intrinsic spatial active neighbors and zero
elsewhere. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    FiniteNonnegativeInfluenceKernelData
      (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact
    { influence := fun target source =>
        if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta
        else 0
      influence_nonneg := by
        intro target source
        split
        · exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
              beta hbeta
        · exact le_rfl
      influence_diagonal_zero := by
        intro source
        have hNotActive :
            source ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source := by
          simp [periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff]
        simp [hNotActive] }

/-- Outside the intrinsic active-neighbor graph the local Harnack influence is
exactly zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_influence_eq_zero_of_not_active
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hNotActive :
      target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta).influence target source = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel,
    hNotActive]

/-- Every nonzero local-Harnack influence edge is an intrinsic spatial active
neighbor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_active_of_influence_ne_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hNe :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source ≠ 0) :
    target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source := by
  by_contra hNotActive
  exact hNe
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_influence_eq_zero_of_not_active
      H beta hbeta target source hNotActive)

/-- Hence every nonzero local-Harnack influence edge is supported on an actual
shared spatial Wilson plaquette. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_sharePlaquette_of_influence_ne_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hNe :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source ≠ 0) :
    periodicHypercubicEvenSpatialSliceLinksSharePlaquette H source target := by
  have hActive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_active_of_influence_ne_zero
      H beta hbeta target source hNe
  exact
    ((periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff
      H source target).mp hActive).2

/-- The actual physical envelope is exactly the local Harnack kernel plus the
source-aligned remote physical vacuum residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remoteResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A).influence target source =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target := by
  rfl

/-- In particular the local Harnack kernel is pointwise below the actual
physical envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_le_envelope
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta).influence target source ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remoteResidual]
  exact le_add_of_nonneg_right
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
      H N hN beta hbeta A source target)

/-- Every source column of the local physical Harnack kernel is bounded by
eighteen times its local coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_columnSum_le_eighteen_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta)
        source ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta
  let zeroResidual :=
    fun _target _source : PeriodicHypercubicEvenSpatialSliceLink H => (0 : ℝ)
  have hEta :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hBound :=
    periodicHypercubicEvenSpatialSlice_influenceColumnSum_le_eighteen_mul_add_residual
      H K.influence zeroResidual
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta)
      hEta
      (by intro target source; simp [zeroResidual])
      (by
        intro target source
        simp [K, zeroResidual,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel])
      source
  simpa [K, zeroResidual, finiteInfluenceKernelColumnSum] using hBound

/-- The actual bounded-test one-link response is controlled by the new local
kernel plus the unchanged remote residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_boundedTest_difference_le_localHarnackKernel_add_remoteResidual
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedSource target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source u)) -
      (∫ g, phi g ∂
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source v))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_boundedTest_difference_le_envelopeKernel
      H N hN beta hbeta B A source distinguishedSource target
      k g₂ u v phi hphi hphiBound
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remoteResidual] at h
  exact h

end

end MathlibAnalytic
end MGAP4D
