import MGAP4D.MathlibAnalytic.FiniteContinuousPositiveWeightConditional
import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelMaximumRow
import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelMaximumColumn
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite value set used by the canonical source influence is exactly the
image of the proof-independent candidate value. -/
theorem finitePositiveWeightConditionalL1SourceValues_eq_candidate_image
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (target source : ι) :
    finitePositiveWeightConditionalL1SourceValues weight target source =
      Finset.univ.image
        (finitePositiveWeightConditionalL1SourceCandidateValue
          weight target source) := by
  classical
  rfl

/-- Away from the diagonal, the canonical non-strict influence is a fixed
finite supremum indexed by all ordered environment pairs. -/
theorem finitePositiveWeightCanonicalNonstrictInfluence_eq_univ_sup'
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (target source : ι)
    (hNe : target ≠ source) :
    finitePositiveWeightCanonicalNonstrictInfluence weight target source =
      Finset.univ.sup' Finset.univ_nonempty
        (finitePositiveWeightConditionalL1SourceCandidateValue
          weight target source) := by
  classical
  rw [finitePositiveWeightCanonicalNonstrictInfluence, if_neg hNe]
  simp only [finitePositiveWeightConditionalL1SourceValues_eq_candidate_image]
  rw [Finset.max'_eq_sup', Finset.sup'_image]
  rfl

/-- Every entry of the canonical non-strict influence matrix varies
continuously with a pointwise continuous strictly positive finite weight
family. -/
theorem continuous_finitePositiveWeightCanonicalNonstrictInfluence
    {X ι G : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : X → (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G,
      Continuous (fun x => weight x configuration))
    (hweightPos : ∀ x configuration, 0 < weight x configuration)
    (target source : ι) :
    Continuous (fun x =>
      finitePositiveWeightCanonicalNonstrictInfluence
        (weight x) target source) := by
  classical
  by_cases hEq : target = source
  · subst source
    simpa using (continuous_const : Continuous (fun _x : X => (0 : ℝ)))
  · have hSup :
        Continuous (fun x =>
          Finset.univ.sup' Finset.univ_nonempty
            (fun pair =>
              finitePositiveWeightConditionalL1SourceCandidateValue
                (weight x) target source pair)) := by
      apply Continuous.finset_sup'_apply Finset.univ_nonempty
      intro pair _hPair
      exact continuous_finitePositiveWeightConditionalL1SourceCandidate
        weight hweight hweightPos target source pair
    convert hSup using 1
    funext x
    exact
      finitePositiveWeightCanonicalNonstrictInfluence_eq_univ_sup'
        (weight x) target source hEq

/-- Pointwise continuous finite influence kernels have continuous row sums. -/
theorem continuous_finiteInfluenceKernelRowSum
    {X ι : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype ι]
    (K : X → FiniteNonnegativeInfluenceKernelData ι)
    (hK : ∀ target source : ι,
      Continuous (fun x => (K x).influence target source))
    (target : ι) :
    Continuous (fun x => finiteInfluenceKernelRowSum (K x) target) := by
  classical
  unfold finiteInfluenceKernelRowSum
  apply continuous_finset_sum
  intro source _hSource
  exact hK target source

/-- Pointwise continuous finite influence kernels have continuous column sums. -/
theorem continuous_finiteInfluenceKernelColumnSum
    {X ι : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype ι]
    (K : X → FiniteNonnegativeInfluenceKernelData ι)
    (hK : ∀ target source : ι,
      Continuous (fun x => (K x).influence target source))
    (source : ι) :
    Continuous (fun x => finiteInfluenceKernelColumnSum (K x) source) := by
  classical
  unfold finiteInfluenceKernelColumnSum
  apply continuous_finset_sum
  intro target _hTarget
  exact hK target source

/-- The exact maximum row sum is the fixed finite supremum of all row sums. -/
theorem finiteInfluenceKernelMaximumRowSum_eq_univ_sup'
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    finiteInfluenceKernelMaximumRowSum K =
      Finset.univ.sup' Finset.univ_nonempty
        (finiteInfluenceKernelRowSum K) := by
  classical
  unfold finiteInfluenceKernelMaximumRowSum
    finiteInfluenceKernelRowSumValues
  rw [Finset.max'_eq_sup', Finset.sup'_image]
  rfl

/-- The exact maximum column sum is the fixed finite supremum of all column
sums. -/
theorem finiteInfluenceKernelMaximumColumnSum_eq_univ_sup'
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : FiniteNonnegativeInfluenceKernelData ι) :
    finiteInfluenceKernelMaximumColumnSum K =
      Finset.univ.sup' Finset.univ_nonempty
        (finiteInfluenceKernelColumnSum K) := by
  classical
  unfold finiteInfluenceKernelMaximumColumnSum
    finiteInfluenceKernelColumnSumValues
  rw [Finset.max'_eq_sup', Finset.sup'_image]
  rfl

/-- The maximum row coefficient of a pointwise continuous finite influence
kernel family is continuous. -/
theorem continuous_finiteInfluenceKernelMaximumRowSum
    {X ι : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : X → FiniteNonnegativeInfluenceKernelData ι)
    (hK : ∀ target source : ι,
      Continuous (fun x => (K x).influence target source)) :
    Continuous (fun x => finiteInfluenceKernelMaximumRowSum (K x)) := by
  classical
  have hSup :
      Continuous (fun x =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun target => finiteInfluenceKernelRowSum (K x) target)) := by
    apply Continuous.finset_sup'_apply Finset.univ_nonempty
    intro target _hTarget
    exact continuous_finiteInfluenceKernelRowSum K hK target
  convert hSup using 1
  funext x
  exact finiteInfluenceKernelMaximumRowSum_eq_univ_sup' (K x)

/-- The maximum column coefficient of a pointwise continuous finite influence
kernel family is continuous. -/
theorem continuous_finiteInfluenceKernelMaximumColumnSum
    {X ι : Type}
    [TopologicalSpace X]
    [DecidableEq ι]
    [Fintype ι]
    [Nonempty ι]
    (K : X → FiniteNonnegativeInfluenceKernelData ι)
    (hK : ∀ target source : ι,
      Continuous (fun x => (K x).influence target source)) :
    Continuous (fun x => finiteInfluenceKernelMaximumColumnSum (K x)) := by
  classical
  have hSup :
      Continuous (fun x =>
        Finset.univ.sup' Finset.univ_nonempty
          (fun source => finiteInfluenceKernelColumnSum (K x) source)) := by
    apply Continuous.finset_sup'_apply Finset.univ_nonempty
    intro source _hSource
    exact continuous_finiteInfluenceKernelColumnSum K hK source
  convert hSup using 1
  funext x
  exact finiteInfluenceKernelMaximumColumnSum_eq_univ_sup' (K x)

end

end MathlibAnalytic
end MGAP4D
