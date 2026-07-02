import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicBinaryPlaquetteProkhorovFullSupport
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

/-- The Bernoulli parameter of a probability law on the canonical Boolean
plaquette carrier: the real mass of the `true` atom. -/
def probabilityMeasure_boolTrueParameter
    (μ : ProbabilityMeasure Bool) : ℝ :=
  (μ : Measure Bool).real {true}

/-- A non-Dirac Boolean probability law has a strictly positive Bernoulli
parameter. -/
theorem probabilityMeasure_boolTrueParameter_pos_of_ne_dirac
    (μ : ProbabilityMeasure Bool)
    (hNonDirac : ∀ b : Bool, (μ : Measure Bool) ≠ Measure.dirac b) :
    0 < probabilityMeasure_boolTrueParameter μ := by
  unfold probabilityMeasure_boolTrueParameter
  apply ENNReal.toReal_pos
  · exact ne_of_gt
      (probabilityMeasure_bool_singleton_pos_of_ne_dirac μ hNonDirac true)
  · finiteness

/-- The real masses of the two Boolean atoms sum to one. -/
theorem probabilityMeasure_bool_real_singleton_sum
    (μ : ProbabilityMeasure Bool) :
    (μ : Measure Bool).real {false} + (μ : Measure Bool).real {true} = 1 := by
  have hUnion : ({false} : Set Bool) ∪ {true} = Set.univ := by
    ext b
    fin_cases b <;> simp
  have hRealUnion :
      (μ : Measure Bool).real (({false} : Set Bool) ∪ {true}) =
        (μ : Measure Bool).real {false} + (μ : Measure Bool).real {true} :=
    measureReal_union (by simp) (measurableSet_singleton true)
  calc
    (μ : Measure Bool).real {false} + (μ : Measure Bool).real {true} =
        (μ : Measure Bool).real (({false} : Set Bool) ∪ {true}) :=
      hRealUnion.symm
    _ = (μ : Measure Bool).real Set.univ :=
      congrArg (fun s : Set Bool => (μ : Measure Bool).real s) hUnion
    _ = 1 := by exact probReal_univ

/-- A non-Dirac Boolean probability law has Bernoulli parameter strictly below
one. -/
theorem probabilityMeasure_boolTrueParameter_lt_one_of_ne_dirac
    (μ : ProbabilityMeasure Bool)
    (hNonDirac : ∀ b : Bool, (μ : Measure Bool) ≠ Measure.dirac b) :
    probabilityMeasure_boolTrueParameter μ < 1 := by
  have hFalsePos : 0 < (μ : Measure Bool).real {false} := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt
        (probabilityMeasure_bool_singleton_pos_of_ne_dirac μ hNonDirac false)
    · finiteness
  have hSum := probabilityMeasure_bool_real_singleton_sum μ
  unfold probabilityMeasure_boolTrueParameter
  linarith

/-- The canonical binary plaquette observable is the indicator of the `true`
atom, so its expectation is the Bernoulli parameter. -/
theorem probabilityMeasure_integral_z2BinaryPlaquetteObservable
    (μ : ProbabilityMeasure Bool) :
    (∫ b : Bool, z2BinaryPlaquetteObservable b ∂(μ : Measure Bool)) =
      probabilityMeasure_boolTrueParameter μ := by
  unfold probabilityMeasure_boolTrueParameter
  have hIndicator :
      (fun b : Bool => z2BinaryPlaquetteObservable b) =
        ({true} : Set Bool).indicator (fun _ => (1 : ℝ)) := by
    funext b
    cases b <;> simp [z2BinaryPlaquetteObservable_apply]
  rw [hIndicator]
  simpa using
    (integral_indicator_one
      (μ := (μ : Measure Bool))
      (s := ({true} : Set Bool))
      (measurableSet_singleton true))

/-- The `0/1` binary plaquette observable is idempotent under pointwise
multiplication. -/
@[simp] theorem z2BinaryPlaquetteObservable_mul_self :
    z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable =
      z2BinaryPlaquetteObservable := by
  ext b
  cases b <;> norm_num [z2BinaryPlaquetteObservable_apply]

/-- The variance of the canonical binary observable is exactly the Bernoulli
variance `p(1-p)`. -/
theorem probabilityMeasure_z2BinaryPlaquetteVariance_eq_bernoulli
    (μ : ProbabilityMeasure Bool) :
    (∫ b : Bool,
        (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) b
          ∂(μ : Measure Bool)) -
      (∫ b : Bool, z2BinaryPlaquetteObservable b
          ∂(μ : Measure Bool)) ^ 2 =
        probabilityMeasure_boolTrueParameter μ *
          (1 - probabilityMeasure_boolTrueParameter μ) := by
  rw [z2BinaryPlaquetteObservable_mul_self]
  rw [probabilityMeasure_integral_z2BinaryPlaquetteObservable]
  ring

/-- The Bernoulli parameter of the automatically extracted continuum plaquette
law. -/
noncomputable def
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliParameter
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) : ℝ :=
  probabilityMeasure_boolTrueParameter D.prokhorovBoolContinuumMeasure

/-- The automatically extracted continuum Bernoulli parameter is positive. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliParameter_pos
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    0 < D.prokhorovBernoulliParameter := by
  apply probabilityMeasure_boolTrueParameter_pos_of_ne_dirac
  exact D.prokhorovBoolContinuumMeasure_ne_dirac

/-- The automatically extracted continuum Bernoulli parameter is strictly less
than one. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliParameter_lt_one
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    D.prokhorovBernoulliParameter < 1 := by
  apply probabilityMeasure_boolTrueParameter_lt_one_of_ne_dirac
  exact D.prokhorovBoolContinuumMeasure_ne_dirac

/-- The continuum observable variance of the automatically selected weak limit
is exactly the variance of its Bernoulli parameter. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovContinuumVariance_eq_bernoulli
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    D.prokhorovWeakLimit.continuumObservableVariance
        D.toPhysicalEmbedding.observable =
      D.prokhorovBernoulliParameter *
        (1 - D.prokhorovBernoulliParameter) := by
  unfold PhysicalFourDimensionalYangMillsWeakLimit.continuumObservableVariance
  change
    (∫ b : Bool,
        (z2BinaryPlaquetteObservable * z2BinaryPlaquetteObservable) b
          ∂(D.prokhorovBoolContinuumMeasure : Measure Bool)) -
      (∫ b : Bool, z2BinaryPlaquetteObservable b
          ∂(D.prokhorovBoolContinuumMeasure : Measure Bool)) ^ 2 =
        probabilityMeasure_boolTrueParameter D.prokhorovBoolContinuumMeasure *
          (1 - probabilityMeasure_boolTrueParameter
            D.prokhorovBoolContinuumMeasure)
  exact probabilityMeasure_z2BinaryPlaquetteVariance_eq_bernoulli
    D.prokhorovBoolContinuumMeasure

/-- The finite-volume bounded-coupling lower bound becomes a quantitative lower
bound for the Bernoulli variance of the extracted continuum law. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliVariance_lower
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Real.exp (-(6 * D.betaUpper)) / 8 ≤
      D.prokhorovBernoulliParameter *
        (1 - D.prokhorovBernoulliParameter) := by
  have hLower :=
    physical_yang_mills_continuumObservableVariance_ge_of_uniform_approximating_ge
      D.prokhorovWeakLimit D.toPhysicalEmbedding.observable
      (Real.exp (-(6 * D.betaUpper)) / 8)
      D.prokhorovObservableNontrivialityCertificate.approximating_variance_ge
  rw [D.prokhorovContinuumVariance_eq_bernoulli] at hLower
  exact hLower

/-- The same variance lower bound gives a direct lower bound on the true-atom
probability. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliLower_le_parameter
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    Real.exp (-(6 * D.betaUpper)) / 8 ≤
      D.prokhorovBernoulliParameter := by
  have hVariance := D.prokhorovBernoulliVariance_lower
  nlinarith [sq_nonneg D.prokhorovBernoulliParameter]

/-- Symmetrically, the true-atom probability is bounded above by one minus the
same positive lower-bound constant. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliParameter_le_one_sub_lower
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    D.prokhorovBernoulliParameter ≤
      1 - Real.exp (-(6 * D.betaUpper)) / 8 := by
  have hVariance := D.prokhorovBernoulliVariance_lower
  nlinarith [sq_nonneg (1 - D.prokhorovBernoulliParameter)]

/-- Quantitative nondegeneracy interval for the automatically extracted
continuum Bernoulli parameter. -/
theorem
    Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData.prokhorovBernoulliParameter_mem_Icc
    (D : Z2PeriodicHypercubicBinaryPlaquetteEmbeddingData) :
    D.prokhorovBernoulliParameter ∈ Set.Icc
      (Real.exp (-(6 * D.betaUpper)) / 8)
      (1 - Real.exp (-(6 * D.betaUpper)) / 8) :=
  ⟨D.prokhorovBernoulliLower_le_parameter,
    D.prokhorovBernoulliParameter_le_one_sub_lower⟩

end

end MathlibAnalytic
end MGAP4D
