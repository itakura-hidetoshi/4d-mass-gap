import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableStrongContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PositiveTimeObservableContractionSemigroup

/-- Scalar continuity input for the actual Osterwalder--Schrader quadratic
expectation of translated observable differences.

This is weaker than assuming Hilbert-valued strong continuity directly.  It is
stated entirely in terms of continuum reflected expectations and is therefore
the natural target for dominated-convergence or weak-convergence arguments. -/
structure OSQuadraticContinuityAtZero
    (T : P.PositiveTimeObservableContractionSemigroup) : Prop where
  continuousAt_zero_osQuadraticDifference :
    ∀ F : D.positiveTimeSubalgebra,
      ContinuousAt
        (fun t : NNReal =>
          P.osQuadraticValue
            (P.carrierOfPositiveTime (T.translate t F) -
              P.carrierOfPositiveTime F)) 0

namespace OSQuadraticContinuityAtZero

variable {T : P.PositiveTimeObservableContractionSemigroup}

private theorem osQuadraticDifference_zero
    (F : D.positiveTimeSubalgebra) :
    P.osQuadraticValue
        (P.carrierOfPositiveTime (T.translate 0 F) -
          P.carrierOfPositiveTime F) = 0 := by
  rw [T.translate_zero]
  simp

private theorem physicalStateDifference_dist_sq
    (t : NNReal) (F : D.positiveTimeSubalgebra) :
    dist
        (P.physicalState (P.carrierOfPositiveTime (T.translate t F)))
        (P.physicalState (P.carrierOfPositiveTime F)) ^ 2 =
      P.osQuadraticValue
        (P.carrierOfPositiveTime (T.translate t F) -
          P.carrierOfPositiveTime F) := by
  let A := P.carrierOfPositiveTime (T.translate t F)
  let B := P.carrierOfPositiveTime F
  have hsub :
      P.physicalState A - P.physicalState B = P.physicalState (A - B) := by
    calc
      P.physicalState A - P.physicalState B =
          P.physicalStateLinearMap A - P.physicalStateLinearMap B := by
        rw [P.physicalStateLinearMap_apply, P.physicalStateLinearMap_apply]
      _ = P.physicalStateLinearMap (A - B) := by
        exact (P.physicalStateLinearMap.map_sub A B).symm
      _ = P.physicalState (A - B) := P.physicalStateLinearMap_apply (A - B)
  calc
    dist (P.physicalState A) (P.physicalState B) ^ 2 =
        ‖P.physicalState A - P.physicalState B‖ ^ 2 := by
      rw [dist_eq_norm]
    _ = ‖P.physicalState (A - B)‖ ^ 2 := by rw [hsub]
    _ = ‖A - B‖ ^ 2 := by rw [P.norm_physicalState]
    _ = P.osQuadraticValue (A - B) := by
      rw [P.osQuadraticValue_eq_norm_sq]

/-- Continuity of the scalar OS quadratic difference implies continuity at time
zero of every represented positive-time observable state. -/
theorem physicalState_continuousAt_zero
    (hT : T.OSQuadraticContinuityAtZero)
    (F : D.positiveTimeSubalgebra) :
    ContinuousAt
      (fun t : NNReal =>
        P.physicalState
          (P.carrierOfPositiveTime (T.translate t F))) 0 := by
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  have hepsilonSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  rcases Metric.continuousAt_iff.mp
      (hT.continuousAt_zero_osQuadraticDifference F)
      (epsilon ^ 2) hepsilonSq with
    ⟨delta, hdelta, hnear⟩
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  have hqNear := hnear ht
  have hqNonneg :
      0 ≤ P.osQuadraticValue
        (P.carrierOfPositiveTime (T.translate t F) -
          P.carrierOfPositiveTime F) := by
    rw [P.osQuadraticValue_eq_norm_sq]
    positivity
  have hqLt :
      P.osQuadraticValue
          (P.carrierOfPositiveTime (T.translate t F) -
            P.carrierOfPositiveTime F) < epsilon ^ 2 := by
    rw [osQuadraticDifference_zero (T := T) F, Real.dist_eq, sub_zero,
      abs_of_nonneg hqNonneg] at hqNear
    exact hqNear
  have hdistSq := physicalStateDifference_dist_sq (T := T) t F
  have hdistNonneg :
      0 ≤ dist
        (P.physicalState (P.carrierOfPositiveTime (T.translate t F)))
        (P.physicalState (P.carrierOfPositiveTime F)) := dist_nonneg
  have hzeroState :
      P.physicalState (P.carrierOfPositiveTime (T.translate 0 F)) =
        P.physicalState (P.carrierOfPositiveTime F) := by
    rw [T.translate_zero]
    rfl
  rw [hzeroState]
  nlinarith

/-- Scalar reflected-expectation continuity generates the exact
`StrongContinuityOnObservableStates` input used by the completed OS semigroup. -/
def toStrongContinuityOnObservableStates
    (hT : T.OSQuadraticContinuityAtZero) :
    T.StrongContinuityOnObservableStates where
  continuousAt_zero_on_physicalState :=
    hT.physicalState_continuousAt_zero

end OSQuadraticContinuityAtZero

/-- The full gauge-invariant observable whose continuum expectation is the
Osterwalder--Schrader quadratic value of the translated observable difference. -/
noncomputable def osQuadraticDifferenceObservable
    (T : P.PositiveTimeObservableContractionSemigroup)
    (t : NNReal) (F : D.positiveTimeSubalgebra) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S :=
  let H : P.Carrier :=
    P.carrierOfPositiveTime (T.translate t F) -
      P.carrierOfPositiveTime F
  D.reflection
      (P.toPositiveTime H :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) *
    (P.toPositiveTime H :
      physicalYangMillsGaugeInvariantObservableSubalgebra S)

/-- Pointwise continuum integrand for the reflected quadratic observable. -/
noncomputable def osQuadraticDifferenceIntegrand
    (T : P.PositiveTimeObservableContractionSemigroup)
    (t : NNReal) (F : D.positiveTimeSubalgebra)
    (A : S.Configuration) : ℝ :=
  ((T.osQuadraticDifferenceObservable t F :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) :
    BoundedContinuousFunction S.Configuration ℝ) A

/-- When the OS state is the physical continuum state, the abstract OS quadratic
value is exactly the integral of the explicit reflected quadratic integrand. -/
theorem osQuadraticValue_difference_eq_continuum_integral
    (T : P.PositiveTimeObservableContractionSemigroup)
    (hOmega :
      P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S)
    (t : NNReal) (F : D.positiveTimeSubalgebra) :
    P.osQuadraticValue
        (P.carrierOfPositiveTime (T.translate t F) -
          P.carrierOfPositiveTime F) =
      ∫ A, T.osQuadraticDifferenceIntegrand t F A
        ∂(S.continuumMeasure : Measure S.Configuration) := by
  rw [P.osQuadraticValue, D.osBilinForm_apply, hOmega,
    physicalYangMillsContinuumGaugeInvariantWeakStarState_apply,
    physicalYangMillsContinuumGaugeInvariantExpectation_apply]
  rfl

/-- Dominated-convergence data for the actual continuum reflected quadratic
integrand at Euclidean time zero. -/
structure OSQuadraticDominatedConvergenceAtZero
    (T : P.PositiveTimeObservableContractionSemigroup) : Prop where
  omega_eq_continuumState :
    P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S
  bound : D.positiveTimeSubalgebra → S.Configuration → ℝ
  bound_integrable : ∀ F,
    Integrable (bound F) (S.continuumMeasure : Measure S.Configuration)
  integrand_aestronglyMeasurable : ∀ F,
    ∀ᶠ t : NNReal in 𝓝 0,
      AEStronglyMeasurable
        (T.osQuadraticDifferenceIntegrand t F)
        (S.continuumMeasure : Measure S.Configuration)
  integrand_bound : ∀ F,
    ∀ᶠ t : NNReal in 𝓝 0,
      ∀ᵐ A ∂(S.continuumMeasure : Measure S.Configuration),
        ‖T.osQuadraticDifferenceIntegrand t F A‖ ≤ bound F A
  integrand_tendsto : ∀ F,
    ∀ᵐ A ∂(S.continuumMeasure : Measure S.Configuration),
      Tendsto
        (fun t : NNReal => T.osQuadraticDifferenceIntegrand t F A)
        (𝓝 0)
        (𝓝 (T.osQuadraticDifferenceIntegrand 0 F A))

/-- Concrete pointwise input for dominated convergence.  The reflected quadratic
integrand is already a bounded continuous function of the configuration, so only
a uniform scalar bound and pointwise Euclidean-time continuity remain. -/
structure OSQuadraticUniformBoundContinuityAtZero
    (T : P.PositiveTimeObservableContractionSemigroup) : Prop where
  omega_eq_continuumState :
    P.omega = physicalYangMillsContinuumGaugeInvariantWeakStarState S
  bound : D.positiveTimeSubalgebra → ℝ
  integrand_bound : ∀ F t A,
    ‖T.osQuadraticDifferenceIntegrand t F A‖ ≤ bound F
  integrand_tendsto : ∀ F A,
    Tendsto
      (fun t : NNReal => T.osQuadraticDifferenceIntegrand t F A)
      (𝓝 0)
      (𝓝 (T.osQuadraticDifferenceIntegrand 0 F A))

namespace OSQuadraticUniformBoundContinuityAtZero

variable {T : P.PositiveTimeObservableContractionSemigroup}

/-- A configuration-independent bound is integrable against the continuum
probability law.  Together with pointwise time continuity it supplies all
measure-theoretic hypotheses of dominated convergence. -/
def toOSQuadraticDominatedConvergenceAtZero
    (H : T.OSQuadraticUniformBoundContinuityAtZero) :
    T.OSQuadraticDominatedConvergenceAtZero where
  omega_eq_continuumState := H.omega_eq_continuumState
  bound := fun F _ => H.bound F
  bound_integrable := by
    intro F
    exact integrable_const (H.bound F)
  integrand_aestronglyMeasurable := by
    intro F
    filter_upwards [] with t
    exact
      (((T.osQuadraticDifferenceObservable t F :
          physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ).continuous).aestronglyMeasurable
  integrand_bound := by
    intro F
    filter_upwards [] with t
    filter_upwards [] with A
    exact H.integrand_bound F t A
  integrand_tendsto := by
    intro F
    filter_upwards [] with A
    exact H.integrand_tendsto F A

end OSQuadraticUniformBoundContinuityAtZero

namespace OSQuadraticDominatedConvergenceAtZero

variable {T : P.PositiveTimeObservableContractionSemigroup}

/-- Dominated convergence of the explicit reflected quadratic integrand produces
the scalar OS quadratic continuity input required by the completed physical
semigroup. -/
theorem toOSQuadraticContinuityAtZero
    (H : T.OSQuadraticDominatedConvergenceAtZero) :
    T.OSQuadraticContinuityAtZero := by
  refine ⟨?_⟩
  intro F
  have hIntegral :
      Tendsto
        (fun t : NNReal =>
          ∫ A, T.osQuadraticDifferenceIntegrand t F A
            ∂(S.continuumMeasure : Measure S.Configuration))
        (𝓝 0)
        (𝓝
          (∫ A, T.osQuadraticDifferenceIntegrand 0 F A
            ∂(S.continuumMeasure : Measure S.Configuration))) :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (H.bound F)
      (H.integrand_aestronglyMeasurable F)
      (H.integrand_bound F)
      (H.bound_integrable F)
      (H.integrand_tendsto F)
  simpa only [T.osQuadraticValue_difference_eq_continuum_integral
    H.omega_eq_continuumState] using hIntegral

end OSQuadraticDominatedConvergenceAtZero

/-- Uniform pointwise control of the explicit reflected quadratic integrand
already implies scalar OS quadratic continuity at zero. -/
theorem OSQuadraticUniformBoundContinuityAtZero.toOSQuadraticContinuityAtZero
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : T.OSQuadraticUniformBoundContinuityAtZero) :
    T.OSQuadraticContinuityAtZero :=
  H.toOSQuadraticDominatedConvergenceAtZero.toOSQuadraticContinuityAtZero

end PositiveTimeObservableContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
