import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteBernoulliParameter
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryClusterPointNondegeneracy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- View a probability measure on the definitionally Boolean physical carrier
as a concrete probability measure on `Bool`. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.boolProbabilityMeasure
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration) :
    ProbabilityMeasure Bool := by
  change ProbabilityMeasure Bool
  exact mu

/-- Bernoulli parameter attached to any candidate probability measure on the
binary physical carrier. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration) : ℝ :=
  probabilityMeasure_boolTrueParameter (D.boolProbabilityMeasure mu)

/-- Every supplied subsequential weak limit remains non-Dirac after exposing the
concrete Boolean carrier. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.boolProbabilityMeasure_ne_dirac_of_subsequence
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu))
    (b : Bool) :
    (D.boolProbabilityMeasure mu : Measure Bool) ≠ Measure.dirac b := by
  let b' : D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration := by
    change Bool
    exact b
  simpa [Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.boolProbabilityMeasure,
    b'] using D.subsequenceContinuumMeasure_ne_dirac f hf mu hmu b'

/-- Every binary plaquette cluster point has Bernoulli parameter strictly above
zero. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    0 < D.clusterPointBernoulliParameter mu := by
  apply probabilityMeasure_boolTrueParameter_pos_of_ne_dirac
  exact D.boolProbabilityMeasure_ne_dirac_of_subsequence f hf mu hmu

/-- Every binary plaquette cluster point has Bernoulli parameter strictly below
one. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter_lt_one
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    D.clusterPointBernoulliParameter mu < 1 := by
  apply probabilityMeasure_boolTrueParameter_lt_one_of_ne_dirac
  exact D.boolProbabilityMeasure_ne_dirac_of_subsequence f hf mu hmu

/-- Both Boolean atoms of every subsequential weak limit carry positive mass. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPoint_singleton_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu))
    (b : Bool) :
    0 < (D.boolProbabilityMeasure mu : Measure Bool) {b} :=
  probabilityMeasure_bool_singleton_pos_of_ne_dirac
    (D.boolProbabilityMeasure mu)
    (D.boolProbabilityMeasure_ne_dirac_of_subsequence f hf mu hmu) b

/-- Consequently every binary plaquette cluster point has full support on the
canonical two-point carrier. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPoint_support_eq_univ
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    (D.boolProbabilityMeasure mu : Measure Bool).support = Set.univ := by
  ext b
  simp only [Set.mem_univ, iff_true]
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hbU : b ∈ U := mem_of_mem_nhds hU
  exact lt_of_lt_of_le
    (D.clusterPoint_singleton_pos f hf mu hmu b)
    (measure_mono (Set.singleton_subset_iff.mpr hbU))

/-- The continuum variance at every binary plaquette cluster point is exactly
its Bernoulli variance. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.subsequenceContinuumVariance_eq_bernoulli
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    (D.subsequenceWeakLimit f hf mu hmu).continuumObservableVariance
        D.toPhysicalEmbedding.observable =
      D.clusterPointBernoulliParameter mu *
        (1 - D.clusterPointBernoulliParameter mu) := by
  unfold PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance
  change
    (∫ b : Bool,
        (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) b
          ∂(D.boolProbabilityMeasure mu : Measure Bool)) -
      (∫ b : Bool, z2BinaryPlaquetteObservable b
          ∂(D.boolProbabilityMeasure mu : Measure Bool)) ^ 2 =
        probabilityMeasure_boolTrueParameter (D.boolProbabilityMeasure mu) *
          (1 - probabilityMeasure_boolTrueParameter
            (D.boolProbabilityMeasure mu))
  exact probabilityMeasure_z2BinaryPlaquetteVariance_eq_bernoulli
    (D.boolProbabilityMeasure mu)

/-- The bounded-coupling lower bound applies uniformly to the Bernoulli variance
of every subsequential weak limit. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliVariance_lower
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    Real.exp (-(6 * D.betaUpper)) / 8 ≤
      D.clusterPointBernoulliParameter mu *
        (1 - D.clusterPointBernoulliParameter mu) := by
  have hLower :=
    physical_yang_mills_continuumObservableVariance_ge_of_uniform_approximating_ge
      (D.subsequenceWeakLimit f hf mu hmu) D.toPhysicalEmbedding.observable
      (Real.exp (-(6 * D.betaUpper)) / 8)
      (D.subsequenceCertificate f hf mu hmu).approximating_variance_ge
  rw [D.subsequenceContinuumVariance_eq_bernoulli f hf mu hmu] at hLower
  exact hLower

/-- Every cluster-point parameter is bounded below by the same finite-volume
variance constant. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliLower_le_parameter
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    Real.exp (-(6 * D.betaUpper)) / 8 ≤
      D.clusterPointBernoulliParameter mu := by
  have hVariance := D.clusterPointBernoulliVariance_lower f hf mu hmu
  nlinarith [sq_nonneg (D.clusterPointBernoulliParameter mu)]

/-- Every cluster-point parameter is bounded above by one minus the same
finite-volume variance constant. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter_le_one_sub_lower
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    D.clusterPointBernoulliParameter mu ≤
      1 - Real.exp (-(6 * D.betaUpper)) / 8 := by
  have hVariance := D.clusterPointBernoulliVariance_lower f hf mu hmu
  nlinarith [sq_nonneg (1 - D.clusterPointBernoulliParameter mu)]

/-- Every subsequential weak-limit parameter lies in one common compact
nondegeneracy interval. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.clusterPointBernoulliParameter_mem_Icc
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (mu : ProbabilityMeasure
      D.toPhysicalEmbedding.toLatticeEmbedding.PhysicalConfiguration)
    (hmu : Tendsto
      (fun n => D.toPhysicalEmbedding.toLatticeEmbedding.embeddedMeasure (f n))
      atTop (nhds mu)) :
    D.clusterPointBernoulliParameter mu ∈ Set.Icc
      (Real.exp (-(6 * D.betaUpper)) / 8)
      (1 - Real.exp (-(6 * D.betaUpper)) / 8) :=
  ⟨D.clusterPointBernoulliLower_le_parameter f hf mu hmu,
    D.clusterPointBernoulliParameter_le_one_sub_lower f hf mu hmu⟩

end

end MathlibAnalytic
end MGAP4D
