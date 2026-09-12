import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelBidirectionalFiniteResponseMonotone
import MGAP4D.MathlibAnalytic.FiniteBidirectionalCrossRecurrenceBarrier
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorBidirectionalBootstrapRecurrence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForPersistentBarrier
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- The actual finite Perron-posterior response coefficient is monotone in the
row or column coefficient on the nonnegative half-line. -/
theorem finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient_mono
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (iterations : ℕ)
    {leftCoefficient rightCoefficient : ℝ}
    (hLeftCoefficient : 0 ≤ leftCoefficient)
    (hCoefficient : leftCoefficient ≤ rightCoefficient) :
    finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
        H β energyIdentity energyNontrivial iterations leftCoefficient ≤
      finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
        H β energyIdentity energyNontrivial iterations rightCoefficient := by
  let sourceMagnitude :=
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) -
      (finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial))⁻¹
  have hCard :
      0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty (FiniteEvenFourTorusSpatialLink H))
  have hEnvelopeMagnitude :
      0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
        β energyIdentity energyNontrivial :=
    finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
      β energyIdentity energyNontrivial hβ hEnergy
  have hSourceMagnitude : 0 ≤ sourceMagnitude := by
    simpa [sourceMagnitude] using
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedSourceTiltAmplitude_nonneg
        β energyIdentity energyNontrivial hβ hEnergy
  simpa [finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient,
    sourceMagnitude] using
    (finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_mono
      hCard iterations hLeftCoefficient hCoefficient
      hEnvelopeMagnitude hSourceMagnitude)

/-- The actual scalar bootstrap map is monotone on nonnegative coefficients. -/
theorem finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap_mono
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations : ℕ)
    {leftCoefficient rightCoefficient : ℝ}
    (hLeftCoefficient : 0 ≤ leftCoefficient)
    (hCoefficient : leftCoefficient ≤ rightCoefficient) :
    finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations leftCoefficient ≤
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations rightCoefficient := by
  have hResponse :=
    finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient_mono
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations hLeftCoefficient hCoefficient
  have hRatio :
      0 ≤ finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  unfold finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hResponse hRatio)

/-- A finite-volume canonical barrier witness.  Once both exact canonical
bootstrap coefficients lie below `barrier` and the scalar bootstrap map sends
`barrier` into itself, all later row and column coefficients remain uniformly
below the same strict barrier. -/
structure Z2PerronPosteriorFiniteBootstrapBarrierCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  responseIterations : ℕ
  startStage : ℕ
  barrier : ℝ
  barrier_nonneg : 0 ≤ barrier
  barrier_lt_one : barrier < 1
  row_start_le :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations startStage ≤ barrier
  column_start_le :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations startStage ≤ barrier
  bootstrapMap_barrier_le :
    finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
      H β energyIdentity energyNontrivial responseIterations barrier ≤ barrier

namespace Z2PerronPosteriorFiniteBootstrapBarrierCertificate

variable
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorFiniteBootstrapBarrierCertificate
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The actual canonical row/column recurrence packaged as an abstract
forward-invariant cross barrier. -/
noncomputable def toCrossRecurrenceBarrier :
    FiniteBidirectionalCrossRecurrenceBarrierData
      (fun stage =>
        finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy
          C.responseIterations stage)
      (fun stage =>
        finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy
          C.responseIterations stage)
      (finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial C.responseIterations) :=
  { startStage := C.startStage
    barrier := C.barrier
    barrier_nonneg := C.barrier_nonneg
    barrier_lt_one := C.barrier_lt_one
    rowCoefficient_nonneg :=
      finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations
    columnCoefficient_nonneg :=
      finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations
    row_start_le := C.row_start_le
    column_start_le := C.column_start_le
    stepMap_mono_on_nonneg := by
      intro left right hLeft hLeftRight
      exact finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap_mono
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations hLeft hLeftRight
    stepMap_barrier_le := C.bootstrapMap_barrier_le
    row_succ_le :=
      finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient_succ_le
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations
    column_succ_le :=
      finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient_succ_le
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations }

/-- Every later canonical maximum row coefficient remains below the barrier. -/
theorem rowCoefficient_add_le
    (offset : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations (C.startStage + offset) ≤ C.barrier :=
  C.toCrossRecurrenceBarrier.rowCoefficient_add_le offset

/-- Every later canonical maximum column coefficient remains below the barrier. -/
theorem columnCoefficient_add_le
    (offset : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations (C.startStage + offset) ≤ C.barrier :=
  C.toCrossRecurrenceBarrier.columnCoefficient_add_le offset

/-- Every later canonical row coefficient is strict. -/
theorem rowCoefficient_add_lt_one
    (offset : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations (C.startStage + offset) < 1 :=
  C.toCrossRecurrenceBarrier.rowCoefficient_add_lt_one offset

/-- Every later canonical column coefficient is strict. -/
theorem columnCoefficient_add_lt_one
    (offset : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations (C.startStage + offset) < 1 :=
  C.toCrossRecurrenceBarrier.columnCoefficient_add_lt_one offset

/-- Every concrete row of every later canonical kernel remains below the same
strict barrier. -/
theorem kernelRowSum_add_le
    (offset : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteInfluenceKernelRowSum
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
          H β energyIdentity energyNontrivial hβ hEnergy
          C.responseIterations (C.startStage + offset))
        target ≤ C.barrier :=
  (finiteEvenFourTorusZ2PerronPosteriorBootstrapRowSum_le
    H β energyIdentity energyNontrivial hβ hEnergy
    C.responseIterations (C.startStage + offset) target).trans
      (C.rowCoefficient_add_le offset)

/-- Every concrete column of every later canonical kernel remains below the
same strict barrier. -/
theorem kernelColumnSum_add_le
    (offset : ℕ)
    (source : FiniteEvenFourTorusSpatialLink H) :
    finiteInfluenceKernelColumnSum
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
          H β energyIdentity energyNontrivial hβ hEnergy
          C.responseIterations (C.startStage + offset))
        source ≤ C.barrier :=
  (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnSum_le
    H β energyIdentity energyNontrivial hβ hEnergy
    C.responseIterations (C.startStage + offset) source).trans
      (C.columnCoefficient_add_le offset)

/-- At every later stage, domination by the canonical kernel turns the actual
posterior canonical non-strict influence matrix directly into strict
Dobrushin data.  No infinite reciprocal resolvent is reintroduced. -/
noncomputable def toDobrushinData
    (offset : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) := by
  let weight :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment
  let stage := C.startStage + offset
  let kernel :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
      H β energyIdentity energyNontrivial hβ hEnergy
      C.responseIterations stage
  let D := finitePositiveWeightCanonicalNonstrictL1MatrixData weight
  have hDomination :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_dominates
      H β energyIdentity energyNontrivial hβ hEnergy
      C.responseIterations stage
  refine D.toDobrushinL1MatrixData
    C.barrier C.barrier_nonneg ?_ C.barrier_lt_one
  intro target
  change
    (∑ source : FiniteEvenFourTorusSpatialLink H,
      finitePositiveWeightCanonicalNonstrictInfluence
        weight target source) ≤ C.barrier
  let boundaryTarget : FiniteEvenFourTorusSpatialLink H :=
    Classical.choice
      (inferInstance : Nonempty (FiniteEvenFourTorusSpatialLink H))
  have hEntry
      (source : FiniteEvenFourTorusSpatialLink H) :
      finitePositiveWeightCanonicalNonstrictInfluence
          weight target source ≤ kernel.influence target source := by
    simpa [weight, kernel] using
      hDomination environment boundaryTarget
        (environment boundaryTarget) target source
  calc
    (∑ source : FiniteEvenFourTorusSpatialLink H,
      finitePositiveWeightCanonicalNonstrictInfluence
        weight target source) ≤
      ∑ source : FiniteEvenFourTorusSpatialLink H,
        kernel.influence target source := by
          apply Finset.sum_le_sum
          intro source _hSource
          exact hEntry source
    _ = finiteInfluenceKernelRowSum kernel target := rfl
    _ ≤ C.barrier := by
      simpa [kernel, stage] using C.kernelRowSum_add_le offset target

/-- Direct strict Dobrushin data at the first stage inside the barrier. -/
noncomputable def toDobrushinDataAtStart
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  C.toDobrushinData 0 environment

end Z2PerronPosteriorFiniteBootstrapBarrierCertificate

/-- All-volume continuation barrier.  The response depth, entry stage, and
strict barrier may depend on the finite side, while every later stage remains
strict and supplies actual posterior Dobrushin data. -/
structure Z2PerronPosteriorFiniteBootstrapBarrierFamilyCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  atVolume :
    ∀ H : ℕ,
      Z2PerronPosteriorFiniteBootstrapBarrierCertificate
        H β energyIdentity energyNontrivial hβ hEnergy

/-- The all-volume barrier family supplies actual strict posterior Dobrushin
data at every finite side and at every offset after the witnessed entry stage. -/
noncomputable def
    Z2PerronPosteriorFiniteBootstrapBarrierFamilyCertificate.toDobrushinData
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorFiniteBootstrapBarrierFamilyCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (H offset : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (C.atVolume H).toDobrushinData offset environment

end

end MathlibAnalytic
end MGAP4D