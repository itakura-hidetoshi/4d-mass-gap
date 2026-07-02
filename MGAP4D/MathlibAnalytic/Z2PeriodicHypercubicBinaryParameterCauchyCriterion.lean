import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryWeakConvergenceCriterion
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Cauchy convergence of the single finite-volume Bernoulli parameter sequence
is sufficient for weak convergence of the full embedded binary plaquette law. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.fullWeakConvergence_of_embeddedBernoulliParameter_cauchy
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (hCauchy : CauchySeq D.embeddedBernoulliParameter) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) := by
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨p, hp⟩
  exact D.fullWeakConvergence_of_embeddedBernoulliParameter_tendsto p hp

/-- On the compact Boolean carrier, full weak convergence to the canonical
Prokhorov law is equivalent to the Cauchy property of one real sequence. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.embeddedMeasure_tendsto_prokhorov_iff_parameter_cauchy
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
        (nhds D.prokhorovSubsequenceLimit.continuumMeasure) ↔
      CauchySeq D.embeddedBernoulliParameter := by
  constructor
  · intro hWeak
    exact
      (D.embeddedMeasure_tendsto_prokhorov_iff_parameter_tendsto.mp hWeak).cauchySeq
  · exact D.fullWeakConvergence_of_embeddedBernoulliParameter_cauchy

/-- Summability of the distances between consecutive Bernoulli parameters is a
concrete sufficient condition for full weak convergence. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.fullWeakConvergence_of_summable_parameter_dist
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (hSummable : Summable fun n : ℕ =>
      dist (D.embeddedBernoulliParameter n)
        (D.embeddedBernoulliParameter n.succ)) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) := by
  apply D.fullWeakConvergence_of_embeddedBernoulliParameter_cauchy
  exact cauchySeq_of_summable_dist hSummable

/-- Equivalently, absolute summability of the consecutive scalar increments
forces convergence of the full embedded probability-law sequence. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.fullWeakConvergence_of_summable_abs_parameter_increment
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (hSummable : Summable fun n : ℕ =>
      |D.embeddedBernoulliParameter (n + 1) -
        D.embeddedBernoulliParameter n|) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) := by
  apply D.fullWeakConvergence_of_summable_parameter_dist
  simpa [Real.dist_eq, Nat.succ_eq_add_one, abs_sub_comm] using hSummable

/-- Under the Cauchy criterion, every supplied subsequential weak limit equals
the canonical Prokhorov limit. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPoint_eq_prokhorov_of_embeddedBernoulliParameter_cauchy
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (hCauchy : CauchySeq D.embeddedBernoulliParameter)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure := by
  rcases cauchySeq_tendsto_of_complete hCauchy with ⟨p, hp⟩
  exact
    D.clusterPoint_eq_prokhorov_of_embeddedBernoulliParameter_tendsto
      p hp f hf μ hμ

/-- Hence the Bernoulli parameter of every cluster point is the canonical
continuum parameter whenever the finite-volume parameter sequence is Cauchy. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter_eq_prokhorov_of_cauchy
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (hCauchy : CauchySeq D.embeddedBernoulliParameter)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    D.clusterPointBernoulliParameter μ = D.prokhorovBernoulliParameter := by
  have hMeasure :=
    D.clusterPoint_eq_prokhorov_of_embeddedBernoulliParameter_cauchy
      hCauchy f hf μ hμ
  subst μ
  rfl

end

end MathlibAnalytic
end MGAP4D
