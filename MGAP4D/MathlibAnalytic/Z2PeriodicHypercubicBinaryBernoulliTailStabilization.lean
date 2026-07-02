import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryParameterCauchyCriterion
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A quantitative tail-stabilization certificate for the one-plaquette
Bernoulli coordinate.

This is the exact finite-volume input needed after reducing Boolean weak
convergence to one scalar sequence. Analytic or stochastic estimates may
supply the certificate by producing a common tail bound that vanishes with the
volume scale. -/
structure BernoulliTailStabilizationCertificate
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  /-- Common upper bound for parameter distances beyond one scale. -/
  tailBound : ℕ → ℝ
  /-- The common tail bound becomes arbitrarily small. -/
  tailBound_vanishes :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, tailBound N < ε
  /-- Any two finite-volume Bernoulli parameters beyond `N` differ by at most
  `tailBound N`. -/
  dist_embeddedBernoulliParameter_le :
    ∀ N m n : ℕ, N ≤ m → N ≤ n →
      dist (D.embeddedBernoulliParameter m)
          (D.embeddedBernoulliParameter n) ≤ tailBound N

namespace BernoulliTailStabilizationCertificate

variable {D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData}

/-- A vanishing common tail bound makes the finite-volume Bernoulli parameter
sequence Cauchy. -/
theorem cauchySeq_embeddedBernoulliParameter
    (C : BernoulliTailStabilizationCertificate D) :
    CauchySeq D.embeddedBernoulliParameter := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rcases C.tailBound_vanishes ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm n hn
  exact lt_of_le_of_lt
    (C.dist_embeddedBernoulliParameter_le N m n hm hn) hN

/-- The certificate upgrades the canonical Prokhorov subsequence to weak
convergence of the full finite-volume embedded measure sequence. -/
theorem fullWeakConvergence
    (C : BernoulliTailStabilizationCertificate D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  D.fullWeakConvergence_of_embeddedBernoulliParameter_cauchy
    C.cauchySeq_embeddedBernoulliParameter

/-- The scalar parameter itself converges to the canonical continuum Bernoulli
parameter. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (C : BernoulliTailStabilizationCertificate D) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) :=
  D.embeddedMeasure_tendsto_prokhorov_iff_parameter_tendsto.mp
    C.fullWeakConvergence

/-- Under one quantitative tail-stabilization certificate, every convergent
strict subsequence has the same continuum probability law. -/
theorem clusterPoint_eq_prokhorov
    (C : BernoulliTailStabilizationCertificate D)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (μ : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hμ : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds μ)) :
    μ = D.prokhorovSubsequenceLimit.continuumMeasure :=
  D.clusterPoint_eq_prokhorov_of_embeddedBernoulliParameter_cauchy
    C.cauchySeq_embeddedBernoulliParameter f hf μ hμ

/-- The certificate simultaneously supplies full weak convergence and
uniqueness of all strict-subsequence weak limits. -/
theorem fullWeakConvergence_and_clusterPointUniqueness
    (C : BernoulliTailStabilizationCertificate D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
        (nhds D.prokhorovSubsequenceLimit.continuumMeasure) ∧
      ∀ (f : ℕ → ℕ), StrictMono f →
        ∀ μ : ProbabilityMeasure
          D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration,
          Tendsto
              (fun n =>
                D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
              atTop (nhds μ) →
            μ = D.prokhorovSubsequenceLimit.continuumMeasure := by
  refine ⟨C.fullWeakConvergence, ?_⟩
  intro f hf μ hμ
  exact C.clusterPoint_eq_prokhorov f hf μ hμ

end BernoulliTailStabilizationCertificate

end Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

end

end MathlibAnalytic
end MGAP4D
