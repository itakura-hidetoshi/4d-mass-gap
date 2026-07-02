import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryClusterPointBernoulli
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- On the Boolean carrier, the mass of the `true` atom determines the whole
probability measure. -/
theorem probabilityMeasure_bool_eq_of_trueParameter_eq
    (μ ν : ProbabilityMeasure Bool)
    (hParameter : probabilityMeasure_boolTrueParameter μ =
      probabilityMeasure_boolTrueParameter ν) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_singleton
  intro b
  cases b
  · have hFalseReal :
        (μ : Measure Bool).real {false} =
          (ν : Measure Bool).real {false} := by
      have hμ := probabilityMeasure_bool_real_singleton_sum μ
      have hν := probabilityMeasure_bool_real_singleton_sum ν
      unfold probabilityMeasure_boolTrueParameter at hParameter
      linarith
    exact (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      hFalseReal
  · unfold probabilityMeasure_boolTrueParameter at hParameter
    exact (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      hParameter

/-- Every real bounded continuous function on `Bool` is affine in the canonical
`0/1` observable. Consequently, its expectation depends affinely on the true
atom probability. -/
theorem probabilityMeasure_integral_bool_bcf_eq_affine
    (μ : ProbabilityMeasure Bool)
    (f : BoundedContinuousFunction Bool ℝ) :
    (∫ b : Bool, f b ∂(μ : Measure Bool)) =
      f false + probabilityMeasure_boolTrueParameter μ *
        (f true - f false) := by
  calc
    (∫ b : Bool, f b ∂(μ : Measure Bool)) =
        ∫ b : Bool,
          f false + (f true - f false) * z2BinaryPlaquetteObservable b
            ∂(μ : Measure Bool) := by
      apply integral_congr_ae
      filter_upwards [] with b
      cases b <;> simp [z2BinaryPlaquetteObservable_apply]
    _ = (∫ _b : Bool, f false ∂(μ : Measure Bool)) +
        ∫ b : Bool,
          (f true - f false) * z2BinaryPlaquetteObservable b
            ∂(μ : Measure Bool) := by
      apply integral_add
      · exact integrable_const _
      · exact
          (z2BinaryPlaquetteObservable.integrable (μ : Measure Bool)).const_mul _
    _ = f false + probabilityMeasure_boolTrueParameter μ *
        (f true - f false) := by
      rw [integral_const_mul]
      rw [probabilityMeasure_integral_z2BinaryPlaquetteObservable]
      simp
      ring

/-- Weak convergence of probability measures on `Bool` is equivalent to
ordinary real convergence of their true-atom Bernoulli parameters. -/
theorem probabilityMeasure_bool_tendsto_iff_trueParameter_tendsto
    {ι : Type*} {F : Filter ι}
    {μs : ι → ProbabilityMeasure Bool}
    {μ : ProbabilityMeasure Bool} :
    Tendsto μs F (nhds μ) ↔
      Tendsto (fun i => probabilityMeasure_boolTrueParameter (μs i)) F
        (nhds (probabilityMeasure_boolTrueParameter μ)) := by
  constructor
  · intro hWeak
    have hObservable :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hWeak)
        z2BinaryPlaquetteObservable
    simpa only [probabilityMeasure_integral_z2BinaryPlaquetteObservable]
      using hObservable
  · intro hParameter
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    have hAffine :
        Tendsto
          (fun i => f false +
            probabilityMeasure_boolTrueParameter (μs i) *
              (f true - f false)) F
          (nhds (f false +
            probabilityMeasure_boolTrueParameter μ *
              (f true - f false))) :=
      tendsto_const_nhds.add (hParameter.mul_const (f true - f false))
    simpa only [probabilityMeasure_integral_bool_bcf_eq_affine]
      using hAffine

/-- The Boolean true-atom parameter is an injective coordinate on probability
measures. -/
theorem probabilityMeasure_boolTrueParameter_injective :
    Function.Injective probabilityMeasure_boolTrueParameter := by
  intro μ ν h
  exact probabilityMeasure_bool_eq_of_trueParameter_eq μ ν h

/-- Concrete Boolean presentation of the finite-volume embedded plaquette law. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.boolEmbeddedMeasure
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) : ProbabilityMeasure Bool :=
  D.boolProbabilityMeasure
    (D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure k)

/-- Finite-volume Bernoulli parameter of the selected binary plaquette law. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedBernoulliParameter
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (k : ℕ) : ℝ :=
  probabilityMeasure_boolTrueParameter (D.boolEmbeddedMeasure k)

/-- For the embedded binary plaquette laws, full weak convergence to a supplied
probability law is exactly convergence of one scalar Bernoulli parameter. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedMeasure_tendsto_iff_parameter_tendsto
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
        (nhds μ) ↔
      Tendsto D.embeddedBernoulliParameter atTop
        (nhds (D.clusterPointBernoulliParameter μ)) := by
  change
    Tendsto D.boolEmbeddedMeasure atTop
        (nhds (D.boolProbabilityMeasure μ)) ↔
      Tendsto D.embeddedBernoulliParameter atTop
        (nhds (D.clusterPointBernoulliParameter μ))
  simpa [Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedBernoulliParameter,
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter]
    using
      (probabilityMeasure_bool_tendsto_iff_trueParameter_tendsto
        (μs := D.boolEmbeddedMeasure)
        (μ := D.boolProbabilityMeasure μ)
        (F := atTop))

/-- In particular, convergence of the full embedded law to the canonical
Prokhorov limit is equivalent to convergence of the finite-volume Bernoulli
parameters to the canonical continuum parameter. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedMeasure_tendsto_prokhorov_iff_parameter_tendsto
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
        (nhds D.prokhorovSubsequenceLimit.continuumMeasure) ↔
      Tendsto D.embeddedBernoulliParameter atTop
        (nhds D.prokhorovBernoulliParameter) := by
  simpa [Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliParameter,
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter]
    using D.embeddedMeasure_tendsto_iff_parameter_tendsto
      D.prokhorovSubsequenceLimit.continuumMeasure

/-- If the finite-volume Bernoulli parameter sequence converges to any real
number, its limit must be the parameter of the canonical Prokhorov cluster
point. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedBernoulliParameter_limit_eq_prokhorov
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (p : ℝ)
    (hParameter : Tendsto D.embeddedBernoulliParameter atTop (nhds p)) :
    p = D.prokhorovBernoulliParameter := by
  have hSubsequenceWeak :
      Tendsto
        (fun n => D.boolEmbeddedMeasure
          (D.prokhorovSubsequenceLimit.subsequence n)) atTop
        (nhds (D.boolProbabilityMeasure
          D.prokhorovSubsequenceLimit.continuumMeasure)) := by
    change Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure
        (D.prokhorovSubsequenceLimit.subsequence n)) atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure)
    exact D.prokhorovSubsequence_weakConvergence
  have hSubsequenceParameter :=
    (probabilityMeasure_bool_tendsto_iff_trueParameter_tendsto.mp
      hSubsequenceWeak)
  have hSubsequenceFromFull :
      Tendsto
        (fun n => D.embeddedBernoulliParameter
          (D.prokhorovSubsequenceLimit.subsequence n)) atTop
        (nhds p) :=
    hParameter.comp D.prokhorovSubsequence_strictMono.tendsto_atTop
  have hSubsequenceToCanonical :
      Tendsto
        (fun n => D.embeddedBernoulliParameter
          (D.prokhorovSubsequenceLimit.subsequence n)) atTop
        (nhds D.prokhorovBernoulliParameter) := by
    simpa [Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedBernoulliParameter,
      Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.boolEmbeddedMeasure,
      Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliParameter,
      Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBoolContinuumMeasure]
      using hSubsequenceParameter
  exact tendsto_nhds_unique hSubsequenceFromFull hSubsequenceToCanonical

/-- Scalar convergence of the finite-volume Bernoulli parameters is sufficient
to upgrade Prokhorov subsequential convergence to weak convergence of the full
embedded measure sequence. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.fullWeakConvergence_of_embeddedBernoulliParameter_tendsto
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (p : ℝ)
    (hParameter : Tendsto D.embeddedBernoulliParameter atTop (nhds p)) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) := by
  have hp := D.embeddedBernoulliParameter_limit_eq_prokhorov p hParameter
  apply D.embeddedMeasure_tendsto_prokhorov_iff_parameter_tendsto.mpr
  simpa [hp] using hParameter

/-- Under scalar parameter convergence, every supplied subsequential weak limit
coincides with the canonical Prokhorov limit. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPoint_eq_prokhorov_of_embeddedBernoulliParameter_tendsto
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (p : ℝ)
    (hParameter : Tendsto D.embeddedBernoulliParameter atTop (nhds p))
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure := by
  have hFull :=
    D.fullWeakConvergence_of_embeddedBernoulliParameter_tendsto p hParameter
  have hCanonicalAlongSubsequence :
      Tendsto
        (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
        atTop (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
    hFull.comp hf.tendsto_atTop
  exact tendsto_nhds_unique hμ hCanonicalAlongSubsequence

end

end MathlibAnalytic
end MGAP4D
