import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackKernelBaseL1Propagation
import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelMaximumRow
import Mathlib.Tactic

/-!
# Remote-row obstruction for the physical influence envelope

The actual physical left influence envelope already splits pointwise into

* the symmetric intrinsic local Harnack kernel;
* the source-aligned remote physical residual.

The local kernel has both row and column sums bounded by the same
volume-independent coefficient.  The high-temperature physical spine already
controls the full envelope columns uniformly.  For an L2 Schur estimate the
remaining directional issue is therefore the row obtained by fixing the
physical target and summing the source-aligned remote residual over sources.

This file names that exact row quantity and proves the full envelope row
decomposition.  It also packages the precise uniform remote-row condition
which would close the maximum-row side.

No remote-row estimate is assumed to hold automatically, no symmetry of the
remote residual is asserted, and no Poincare or spectral-gap conclusion is
drawn here.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalEnvelopeRemoteRowSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalEnvelopeRemoteRowSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

local instance physicalEnvelopeRemoteRowSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The row-oriented remote obstruction: fix the physical target and sum the
source-aligned residual over all physical sources. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
      H N hN beta hbeta A source target

/-- Every remote residual row sum is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
        H N hN beta hbeta A target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
  exact
    Finset.sum_nonneg fun source _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
        H N hN beta hbeta A source target

/-- Exact row decomposition of the actual physical envelope into the local
Harnack row and the source-aligned remote row obstruction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_rowSum_eq_localHarnack_add_remoteRow
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        target =
      finiteInfluenceKernelRowSum
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta)
          target +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
          H N hN beta hbeta A target := by
  classical
  unfold finiteInfluenceKernelRowSum
  simp_rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remoteResidual]
  rw [Finset.sum_add_distrib]
  rfl

/-- Consequently every actual physical-envelope row is bounded by the
volume-independent local eighteen-neighbor coefficient plus the explicit
remote row obstruction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_rowSum_le_eighteen_mul_add_remoteRow
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        target ≤
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
          H N hN beta hbeta A target := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_rowSum_eq_localHarnack_add_remoteRow]
  exact
    add_le_add_left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_rowSum_le_eighteen_mul
        H beta hbeta target)
      _

/-- Volume/background/target-uniform bound on the row-oriented remote
residual.  This is a named mathematical obligation, not an asserted fact. -/
def
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (rho : ℝ) : Prop :=
  ∀ (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
        H N hN beta hbeta A target ≤
      rho

/-- A uniform remote-row bound gives the corresponding full physical-envelope
row bound at every finite volume and background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_rowSum_le_of_uniformRemoteRow
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (hRemote :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
        N hN beta hbeta rho)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteInfluenceKernelRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A)
        target ≤
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        rho := by
  have hRow :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_rowSum_le_eighteen_mul_add_remoteRow
      H N hN beta hbeta A target
  exact hRow.trans (add_le_add_right (hRemote H A target) _)

/-- The same uniform remote-row bound controls the exact maximum row sum of
every finite-volume/background physical envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumRow_le_of_uniformRemoteRow
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (hRemote :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
        N hN beta hbeta rho)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) ≤
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        rho := by
  apply finiteInfluenceKernelMaximumRowSum_le_of_forall
  intro target
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_rowSum_le_of_uniformRemoteRow
      N hN beta hbeta rho hRemote H A target

/-- If the local-plus-remote row coefficient is strictly below one, every
finite-volume/background physical envelope has maximum row strictly below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumRow_lt_one_of_uniformRemoteRow
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (hRemote :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
        N hN beta hbeta rho)
    (hStrict :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        rho < 1)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) < 1 := by
  exact
    lt_of_le_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumRow_le_of_uniformRemoteRow
        N hN beta hbeta rho hRemote H A)
      hStrict

end

end MGAP4D.MathlibAnalytic
