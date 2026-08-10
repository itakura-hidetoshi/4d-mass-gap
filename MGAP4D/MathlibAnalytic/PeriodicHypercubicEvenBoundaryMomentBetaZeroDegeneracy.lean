import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentAdjointSynthesis
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance betaZeroBoundaryMomentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroBoundaryMomentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroBoundaryMomentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroBoundaryMomentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroBoundaryMomentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- At zero coupling the completed positive Wilson Gram feature loses all
boundary dependence.  The partition-function normalization is deliberately
left unevaluated: only independence of the boundary configuration is needed. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_beta_zero_boundary_independent
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h0 : 0 ≤ (0 : ℝ))
    (b₁ b₂ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN 0 h0 b₁ x =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN 0 h0 b₂ x := by
  simp [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature,
    periodicHypercubicEvenBoundaryGramCoefficient,
    periodicHypercubicEvenBoundarySpatialCrossingWilsonBoltzmannWeight,
    periodicHypercubicEvenSpatialCrossingWilsonBoltzmannWeight,
    periodicHypercubicEvenBoundaryCompletedPositiveWilsonAmplitude,
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude,
    periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude,
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight]

/-- Therefore every zero-coupling observable Gram feature is boundary-
independent pointwise. -/
theorem periodicHypercubicEvenBoundaryObservableGramFeature_beta_zero_boundary_independent
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h0 : 0 ≤ (0 : ℝ))
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ)
    (b₁ b₂ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN 0 h0 f b₁ x =
      periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN 0 h0 f b₂ x := by
  unfold periodicHypercubicEvenBoundaryObservableGramFeature
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_beta_zero_boundary_independent
    H N hN h0 b₁ b₂ x]

/-- Consequently the raw zero-coupling Wilson boundary moment is a constant
function of the reflection-fixed boundary, for every open-half observable.

This is a genuine degeneracy statement about the finite Wilson Gram kernel. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_beta_zero_boundary_independent
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h0 : 0 ≤ (0 : ℝ))
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ)
    (b₁ b₂ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryObservableMoment H N hN 0 h0 f b₁ =
      periodicHypercubicEvenBoundaryObservableMoment H N hN 0 h0 f b₂ := by
  unfold periodicHypercubicEvenBoundaryObservableMoment
  apply integral_congr_ae
  filter_upwards [] with x
  exact periodicHypercubicEvenBoundaryObservableGramFeature_beta_zero_boundary_independent
    H N hN h0 f b₁ b₂ x

/-- Equivalent packaged form: every zero-coupling boundary moment has a single
scalar value on the entire boundary configuration space. -/
theorem periodicHypercubicEvenBoundaryObservableMoment_beta_zero_exists_constant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (h0 : 0 ≤ (0 : ℝ))
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ) :
    ∃ c : ℝ, ∀ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
      periodicHypercubicEvenBoundaryObservableMoment H N hN 0 h0 f b = c := by
  let b₀ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N :=
    fun _ => 1
  refine ⟨periodicHypercubicEvenBoundaryObservableMoment H N hN 0 h0 f b₀, ?_⟩
  intro b
  exact periodicHypercubicEvenBoundaryObservableMoment_beta_zero_boundary_independent
    H N hN h0 f b b₀

end

end MathlibAnalytic
end MGAP4D
