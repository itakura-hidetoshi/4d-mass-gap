import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorBidirectionalBootstrapRecurrence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForEnvelope
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- Finite parameter space indexing all actual target-fiber posterior
canonical influence entries at one finite volume and coupling. -/
abbrev FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter
    (H : ℕ) :=
  (FiniteEvenFourTorusZ2SliceConfiguration H ×
      FiniteEvenFourTorusSpatialLink H) × Z2Gauge

/-- All actual canonical non-strict influence values at one ordered pair of
spatial links, ranging over every environment, boundary target, and boundary
replacement. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) : Finset ℝ := by
  classical
  exact Finset.univ.image fun parameter :
      FiniteEvenFourTorusZ2PerronPosteriorEnvelopeParameter H =>
    finitePositiveWeightCanonicalNonstrictInfluence
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (Function.update parameter.1.1 parameter.1.2 parameter.2))
      target source

/-- The finite actual-value set is nonempty. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues_nonempty
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
      H β energyIdentity energyNontrivial hβ hEnergy target source).Nonempty := by
  classical
  unfold finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
  exact Finset.univ_nonempty.image _

/-- Exact environment-uniform posterior canonical influence envelope.  The
diagonal is kept definitionally zero; off the diagonal this is the finite
maximum over every actual target fiber. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  if target = source then 0 else
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
      H β energyIdentity energyNontrivial hβ hEnergy target source).max'
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues_nonempty
          H β energyIdentity energyNontrivial hβ hEnergy target source)

/-- Every actual posterior canonical entry belongs to the envelope value set. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalInfluence_mem_envelopeValues
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (boundaryTarget target source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    finitePositiveWeightCanonicalNonstrictInfluence
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (Function.update environment boundaryTarget g))
        target source ∈
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
        H β energyIdentity energyNontrivial hβ hEnergy target source := by
  classical
  unfold finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
  apply Finset.mem_image.mpr
  exact ⟨((environment, boundaryTarget), g), Finset.mem_univ _, rfl⟩

/-- The exact envelope is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
      H β energyIdentity energyNontrivial hβ hEnergy target source := by
  by_cases hEq : target = source
  · simp [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence, hEq]
  · rw [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence,
      if_neg hEq]
    let environment : FiniteEvenFourTorusZ2SliceConfiguration H :=
      fun _ => 1
    let boundaryTarget : FiniteEvenFourTorusSpatialLink H :=
      Classical.choice
        (inferInstance : Nonempty (FiniteEvenFourTorusSpatialLink H))
    let g : Z2Gauge := 1
    have hEntryNonneg :
        0 ≤ finitePositiveWeightCanonicalNonstrictInfluence
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            (Function.update environment boundaryTarget g))
          target source :=
      finitePositiveWeightCanonicalNonstrictInfluence_nonneg _ target source
    exact hEntryNonneg.trans
      (Finset.le_max'
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
          H β energyIdentity energyNontrivial hβ hEnergy target source)
        _
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalInfluence_mem_envelopeValues
          H β energyIdentity energyNontrivial hβ hEnergy
          environment boundaryTarget target source g))

/-- The exact envelope has zero diagonal. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence_diagonal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
      H β energyIdentity energyNontrivial hβ hEnergy target target = 0 := by
  simp [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence]

/-- Exact finite nonnegative kernel enveloping all actual posterior canonical
non-strict influence matrices. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    FiniteNonnegativeInfluenceKernelData
      (FiniteEvenFourTorusSpatialLink H) :=
  { influence :=
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
        H β energyIdentity energyNontrivial hβ hEnergy
    influence_nonneg :=
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
    influence_diagonal_zero :=
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence_diagonal
        H β energyIdentity energyNontrivial hβ hEnergy }

/-- The exact envelope dominates every actual target-fiber posterior canonical
matrix. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
        H β energyIdentity energyNontrivial hβ hEnergy) := by
  intro environment boundaryTarget g target source
  by_cases hEq : target = source
  · subst source
    simp [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel]
  · change
      finitePositiveWeightCanonicalNonstrictInfluence
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            (Function.update environment boundaryTarget g))
          target source ≤
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
          H β energyIdentity energyNontrivial hβ hEnergy target source
    rw [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence,
      if_neg hEq]
    exact Finset.le_max'
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeValues
        H β energyIdentity energyNontrivial hβ hEnergy target source)
      _
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalInfluence_mem_envelopeValues
        H β energyIdentity energyNontrivial hβ hEnergy
        environment boundaryTarget target source g)

/-- Minimality of the exact finite maximum: every nonnegative kernel that
dominates all actual target fibers also dominates the canonical envelope
entrywise. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_le_of_dominates
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
        H β energyIdentity energyNontrivial hβ hEnergy).influence
        target source ≤ kernel.influence target source := by
  by_cases hEq : target = source
  · subst source
    simp [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel,
      kernel.influence_nonneg]
  · change
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence
          H β energyIdentity energyNontrivial hβ hEnergy target source ≤
        kernel.influence target source
    rw [finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeInfluence,
      if_neg hEq]
    rw [Finset.max'_le_iff]
    intro value hValue
    rcases Finset.mem_image.mp hValue with
      ⟨parameter, _hParameter, rfl⟩
    exact hDomination
      parameter.1.1 parameter.1.2 parameter.2 target source

/-- Exact maximum row coefficient of the actual environment-uniform envelope. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) : ℝ :=
  finiteInfluenceKernelMaximumRowSum
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Exact maximum column coefficient of the actual environment-uniform
envelope. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) : ℝ :=
  finiteInfluenceKernelMaximumColumnSum
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The exact envelope row coefficient is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy :=
  finiteInfluenceKernelMaximumRowSum_nonneg _

/-- The exact envelope column coefficient is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy :=
  finiteInfluenceKernelMaximumColumnSum_nonneg _

/-- Exact self-consistent row bootstrap inequality for the actual canonical
envelope. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient_le_bootstrapMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy ≤
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy) := by
  let kernel :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy
  let next :=
    finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
      H β energyIdentity energyNontrivial hβ hEnergy
      kernel responseIterations
  have hNextDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy next :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy_next
      H β energyIdentity energyNontrivial hβ hEnergy
      kernel responseIterations
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
        H β energyIdentity energyNontrivial hβ hEnergy)
  apply finiteInfluenceKernelMaximumRowSum_le_of_forall
  intro target
  calc
    finiteInfluenceKernelRowSum kernel target ≤
        finiteInfluenceKernelRowSum next target := by
      unfold finiteInfluenceKernelRowSum
      apply Finset.sum_le_sum
      intro source _hSource
      exact
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_le_of_dominates
          H β energyIdentity energyNontrivial hβ hEnergy
          next hNextDomination target source
    _ ≤ finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy) :=
      finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext_rowSum_le
        H β energyIdentity energyNontrivial hβ hEnergy
        kernel responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient_nonneg
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteInfluenceKernelColumnSum_le_maximum kernel)
        target

/-- Exact self-consistent column bootstrap inequality for the actual canonical
envelope. -/
theorem finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient_le_bootstrapMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy ≤
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy) := by
  let kernel :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy
  let next :=
    finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
      H β energyIdentity energyNontrivial hβ hEnergy
      kernel responseIterations
  have hNextDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy next :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy_next
      H β energyIdentity energyNontrivial hβ hEnergy
      kernel responseIterations
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
        H β energyIdentity energyNontrivial hβ hEnergy)
  apply finiteInfluenceKernelMaximumColumnSum_le_of_forall
  intro source
  calc
    finiteInfluenceKernelColumnSum kernel source ≤
        finiteInfluenceKernelColumnSum next source := by
      unfold finiteInfluenceKernelColumnSum
      apply Finset.sum_le_sum
      intro target _hTarget
      exact
        finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_le_of_dominates
          H β energyIdentity energyNontrivial hβ hEnergy
          next hNextDomination target source
    _ ≤ finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy) :=
      finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext_columnSum_le
        H β energyIdentity energyNontrivial hβ hEnergy
        kernel responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient_nonneg
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteInfluenceKernelRowSum_le_maximum kernel)
        source

end

end MathlibAnalytic
end MGAP4D