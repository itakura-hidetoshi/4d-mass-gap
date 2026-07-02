import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryWeakConvergenceCriterion
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set Topology

noncomputable section

namespace Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData

/-- A quantitative tail-stabilization certificate for the one-plaquette
Bernoulli coordinate.

This is the exact finite-volume input needed after the Boolean weak-convergence
reduction.  Strong-coupling cluster expansion or stochastic-ergodic estimates
may discharge the certificate by producing a tail bound that vanishes with the
volume scale. -/
structure BernoulliTailStabilizationCertificate
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) where
  /-- Common upper bound for all parameter distances beyond one scale. -/
  tailBound : ℕ → ℝ
  /-- The tail bound becomes arbitrarily small. -/
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

/-- A vanishing quantitative tail bound makes the finite-volume Bernoulli
parameter sequence Cauchy. -/
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

/-- Completeness of `ℝ` converts the quantitative stabilization certificate
into an actual scalar limit. -/
theorem exists_embeddedBernoulliParameter_limit
    (C : BernoulliTailStabilizationCertificate D) :
    ∃ p : ℝ,
      Tendsto D.embeddedBernoulliParameter atTop (nhds p) :=
  cauchySeq_tendsto_of_complete C.cauchySeq_embeddedBernoulliParameter

/-- The scalar limit selected by any tail-stabilization certificate is the
canonical Prokhorov Bernoulli parameter. -/
theorem embeddedBernoulliParameter_tendsto_prokhorov
    (C : BernoulliTailStabilizationCertificate D) :
    Tendsto D.embeddedBernoulliParameter atTop
      (nhds D.prokhorovBernoulliParameter) := by
  rcases C.exists_embeddedBernoulliParameter_limit with ⟨p, hp⟩
  have hpEq := D.embeddedBernoulliParameter_limit_eq_prokhorov p hp
  simpa [hpEq] using hp

/-- Quantitative stabilization of the one-plaquette Bernoulli coordinate
upgrades the canonical Prokhorov subsequence to weak convergence of the full
finite-volume embedded law sequence. -/
theorem fullWeakConvergence
    (C : BernoulliTailStabilizationCertificate D) :
    Tendsto D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure atTop
      (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
  D.embeddedMeasure_tendsto_prokhorov_iff_parameter_tendsto.mpr
    C.embeddedBernoulliParameter_tendsto_prokhorov

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
    μ = D.prokhorovSubsequenceLimit.continuumMeasure := by
  have hCanonicalAlongSubsequence :
      Tendsto
        (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
        atTop (nhds D.prokhorovSubsequenceLimit.continuumMeasure) :=
    C.fullWeakConvergence.comp hf.tendsto_atTop
  exact tendsto_nhds_unique hμ hCanonicalAlongSubsequence

/-- The stabilization certificate simultaneously supplies full weak convergence
and uniqueness of all strict-subsequence weak limits. -/
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
