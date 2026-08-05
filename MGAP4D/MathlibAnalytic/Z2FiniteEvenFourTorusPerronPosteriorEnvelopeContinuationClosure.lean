import MGAP4D.MathlibAnalytic.FiniteContinuousBidirectionalSelfBootstrapBarrier
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorAsymptoticBootstrapMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForContinuation
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- Fixed-volume analytic continuation input for the exact actual posterior
envelope.  The only model-facing analytic obligation is to extend the exact
maximum row and column coefficients continuously to coupling zero, where they
start strictly inside the declared barrier.  All finite maxima, response-depth
selection, self-bootstrap, first-exit, and Dobrushin conversion are generated
downstream. -/
structure Z2PerronPosteriorCanonicalEnvelopeContinuationData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (barrier : ℝ) where
  rowCoefficient : ℝ → ℝ
  columnCoefficient : ℝ → ℝ
  rowCoefficient_continuousOn :
    ContinuousOn rowCoefficient (Set.Icc 0 β)
  columnCoefficient_continuousOn :
    ContinuousOn columnCoefficient (Set.Icc 0 β)
  rowCoefficient_zero_lt : rowCoefficient 0 < barrier
  columnCoefficient_zero_lt : columnCoefficient 0 < barrier
  rowCoefficient_eq_envelope :
    ∀ parameter : ℝ,
      ∀ hParameter : parameter ∈ Set.Ioc 0 β,
        rowCoefficient parameter =
          finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
            H parameter energyIdentity energyNontrivial
            hParameter.1 hEnergy
  columnCoefficient_eq_envelope :
    ∀ parameter : ℝ,
      ∀ hParameter : parameter ∈ Set.Ioc 0 β,
        columnCoefficient parameter =
          finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
            H parameter energyIdentity energyNontrivial
            hParameter.1 hEnergy
  asymptoticBootstrapMap_lt :
    ∀ parameter : ℝ,
      ∀ hParameter : parameter ∈ Set.Ioc 0 β,
        finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap
          parameter energyIdentity energyNontrivial barrier < barrier

namespace Z2PerronPosteriorCanonicalEnvelopeContinuationData

variable
    {H : ℕ}
    {β energyIdentity energyNontrivial barrier : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorCanonicalEnvelopeContinuationData
      H β energyIdentity energyNontrivial hβ hEnergy barrier)

/-- At every positive continuation parameter, some finite response depth sends
the common barrier strictly inside itself. -/
theorem exists_responseIterations
    (parameter : ℝ)
    (hParameter : parameter ∈ Set.Ioc 0 β)
    (hBarrierNonneg : 0 ≤ barrier)
    (hBarrierLtOne : barrier < 1) :
    ∃ responseIterations : ℕ,
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H parameter energyIdentity energyNontrivial
        responseIterations barrier < barrier :=
  exists_finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap_lt
    H parameter energyIdentity energyNontrivial barrier barrier
    hParameter.1 hEnergy hBarrierNonneg hBarrierLtOne
    (C.asymptoticBootstrapMap_lt parameter hParameter)

/-- Canonical finite response-depth selector along the continuation path. -/
noncomputable def responseIterations
    (hBarrierNonneg : 0 ≤ barrier)
    (hBarrierLtOne : barrier < 1)
    (parameter : ℝ) : ℕ :=
  if hParameter : parameter ∈ Set.Ioc 0 β then
    Classical.choose
      (C.exists_responseIterations parameter hParameter
        hBarrierNonneg hBarrierLtOne)
  else 0

/-- The selected response depth realizes the strict map inequality at every
positive continuation parameter. -/
theorem bootstrapMap_barrier_lt
    (hBarrierNonneg : 0 ≤ barrier)
    (hBarrierLtOne : barrier < 1)
    (parameter : ℝ)
    (hParameter : parameter ∈ Set.Ioc 0 β) :
    finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H parameter energyIdentity energyNontrivial
        (C.responseIterations hBarrierNonneg hBarrierLtOne parameter)
        barrier < barrier := by
  simp only [responseIterations, dif_pos hParameter]
  exact Classical.choose_spec
    (C.exists_responseIterations parameter hParameter
      hBarrierNonneg hBarrierLtOne)

/-- Specialization of the generic continuous first-exit theorem to the exact
actual Perron posterior envelope. -/
noncomputable def toContinuousSelfBootstrapBarrier
    (hBarrierNonneg : 0 ≤ barrier)
    (hBarrierLtOne : barrier < 1) :
    FiniteContinuousBidirectionalSelfBootstrapBarrierData :=
  { upperParameter := β
    upperParameter_pos := hβ
    barrier := barrier
    barrier_nonneg := hBarrierNonneg
    rowCoefficient := C.rowCoefficient
    columnCoefficient := C.columnCoefficient
    rowCoefficient_continuousOn := C.rowCoefficient_continuousOn
    columnCoefficient_continuousOn := C.columnCoefficient_continuousOn
    rowCoefficient_zero_lt := C.rowCoefficient_zero_lt
    columnCoefficient_zero_lt := C.columnCoefficient_zero_lt
    stepMap := fun parameter coefficient =>
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H parameter energyIdentity energyNontrivial
        (C.responseIterations hBarrierNonneg hBarrierLtOne parameter)
        coefficient
    rowCoefficient_nonneg := by
      intro parameter hParameter
      rw [C.rowCoefficient_eq_envelope parameter hParameter]
      exact
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient_nonneg
          H parameter energyIdentity energyNontrivial hParameter.1 hEnergy
    columnCoefficient_nonneg := by
      intro parameter hParameter
      rw [C.columnCoefficient_eq_envelope parameter hParameter]
      exact
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient_nonneg
          H parameter energyIdentity energyNontrivial hParameter.1 hEnergy
    stepMap_mono_on_nonneg := by
      intro parameter hParameter left right hLeft hLeftRight
      exact
        finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap_mono
          H parameter energyIdentity energyNontrivial
          hParameter.1 hEnergy
          (C.responseIterations hBarrierNonneg hBarrierLtOne parameter)
          hLeft hLeftRight
    stepMap_barrier_lt := by
      intro parameter hParameter
      exact C.bootstrapMap_barrier_lt
        hBarrierNonneg hBarrierLtOne parameter hParameter
    row_self_le := by
      intro parameter hParameter
      rw [C.rowCoefficient_eq_envelope parameter hParameter,
        C.columnCoefficient_eq_envelope parameter hParameter]
      exact
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient_le_bootstrapMap
          H parameter energyIdentity energyNontrivial
          hParameter.1 hEnergy
          (C.responseIterations hBarrierNonneg hBarrierLtOne parameter)
    column_self_le := by
      intro parameter hParameter
      rw [C.columnCoefficient_eq_envelope parameter hParameter,
        C.rowCoefficient_eq_envelope parameter hParameter]
      exact
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient_le_bootstrapMap
          H parameter energyIdentity energyNontrivial
          hParameter.1 hEnergy
          (C.responseIterations hBarrierNonneg hBarrierLtOne parameter) }

/-- The actual endpoint envelope row and column coefficients lie strictly below
the continuation barrier. -/
theorem endpoint_envelopeCoefficients_lt
    (hBarrierNonneg : 0 ≤ barrier)
    (hBarrierLtOne : barrier < 1) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy < barrier ∧
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy < barrier := by
  have hEndpoint :=
    (C.toContinuousSelfBootstrapBarrier
      hBarrierNonneg hBarrierLtOne).endpoint_coefficients_lt_barrier
  have hMembership : β ∈ Set.Ioc 0 β := ⟨hβ, le_rfl⟩
  rw [C.rowCoefficient_eq_envelope β hMembership,
    C.columnCoefficient_eq_envelope β hMembership] at hEndpoint
  exact hEndpoint

/-- Every endpoint posterior weight receives strict Dobrushin data directly
from the exact environment-uniform envelope. -/
noncomputable def toDobrushinData
    (hBarrierNonneg : 0 ≤ barrier)
    (hBarrierLtOne : barrier < 1)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) := by
  let weight :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment
  let D := finitePositiveWeightCanonicalNonstrictL1MatrixData weight
  let kernel :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy
  have hEnvelopeStrict :=
    (C.endpoint_envelopeCoefficients_lt
      hBarrierNonneg hBarrierLtOne).1
  refine D.toDobrushinL1MatrixData
    barrier hBarrierNonneg ?_ hBarrierLtOne
  intro target
  let boundaryTarget : FiniteEvenFourTorusSpatialLink H :=
    Classical.choice
      (inferInstance : Nonempty (FiniteEvenFourTorusSpatialLink H))
  have hEntry
      (source : FiniteEvenFourTorusSpatialLink H) :
      finitePositiveWeightCanonicalNonstrictInfluence
          weight target source ≤ kernel.influence target source := by
    have hDominates :=
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
        H β energyIdentity energyNontrivial hβ hEnergy
        environment boundaryTarget (environment boundaryTarget)
        target source
    simpa [weight, kernel, Function.update_same] using hDominates
  calc
    finitePositiveWeightNonstrictInfluenceRowSum D target ≤
        finiteInfluenceKernelRowSum kernel target := by
      unfold finitePositiveWeightNonstrictInfluenceRowSum
        finiteInfluenceKernelRowSum D
      apply Finset.sum_le_sum
      intro source _hSource
      exact hEntry source
    _ ≤ finiteInfluenceKernelMaximumRowSum kernel :=
      finiteInfluenceKernelRowSum_le_maximum kernel target
    _ < barrier := by
      simpa [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient,
        kernel] using hEnvelopeStrict

end Z2PerronPosteriorCanonicalEnvelopeContinuationData

/-- All-volume continuation package.  The common barrier and physical coupling
are volume-independent; only the finite-dimensional continuous envelope
extensions and selected finite response depths vary with the side. -/
structure Z2PerronPosteriorCanonicalEnvelopeContinuationFamilyData
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  barrier : ℝ
  barrier_nonneg : 0 ≤ barrier
  barrier_lt_one : barrier < 1
  atVolume :
    ∀ H : ℕ,
      Z2PerronPosteriorCanonicalEnvelopeContinuationData
        H β energyIdentity energyNontrivial hβ hEnergy barrier

namespace Z2PerronPosteriorCanonicalEnvelopeContinuationFamilyData

variable
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorCanonicalEnvelopeContinuationFamilyData
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Uniform strict endpoint row and column bounds at every finite side. -/
theorem endpoint_envelopeCoefficients_lt
    (H : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy < C.barrier ∧
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy < C.barrier :=
  (C.atVolume H).endpoint_envelopeCoefficients_lt
    C.barrier_nonneg C.barrier_lt_one

/-- Actual strict posterior Dobrushin data at every finite side and every
boundary environment. -/
noncomputable def toDobrushinData
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (C.atVolume H).toDobrushinData
    C.barrier_nonneg C.barrier_lt_one environment

end Z2PerronPosteriorCanonicalEnvelopeContinuationFamilyData

end

end MathlibAnalytic
end MGAP4D