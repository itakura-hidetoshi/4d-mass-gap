import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberAEBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorVariationPropagation
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic

/-!
# Genuine ground-state fibers and posterior conditional laws

The historical genuine joint fiber measure uses an L2 vacuum representative.
The posterior conditional law uses the positive continuous representative.
PR #5151 already identifies their unnormalized fiber weights for Haar-a.e.
left and off-target contexts, but retains the extra positive left-dependent
factor in the continuous-compatible weight.

This file removes precisely that normalization seam.  A positive scalar c
cancels from the normalized weight c * exp(f).  In the actual model,

  c(left) = ||T_phys||^(-1) * Omega_cont(left) > 0.

The continuous-compatible fiber measure is therefore exactly the posterior
one-link conditional law.  Combining this pointwise normalization identity
with the historical a.e. bridge identifies genuine fiber integration with the
posterior bounded-continuous conditional expectation.

The full-measure contexts are independent of the bounded-continuous test.
No equality on exceptional fixed fibers, joint-L2 operator identification,
stagewise oscillation tail, physicality/commutation bound, or Euclidean-time
identification is asserted here.  In particular the strict-interval scaling
no-go from PR #5207 is not bypassed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A strictly positive scalar cancels exactly when an exponential weight is
normalized.  The result is mathlib's tilted measure, with no comparison loss. -/
theorem doobWeightedMeasure_ofReal_mul_exp_eq_tilted
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NeZero μ]
    (f : α → ℝ) (hf : Integrable (fun x => Real.exp (f x)) μ)
    (c : ℝ) (hc : 0 < c) :
    doobWeightedMeasure μ (fun x => ENNReal.ofReal (c * Real.exp (f x))) =
      μ.tilted f := by
  have hInt : Integrable (fun x => c * Real.exp (f x)) μ :=
    hf.const_mul c
  have hMassPos : 0 < c * ∫ x, Real.exp (f x) ∂μ :=
    mul_pos hc (integral_exp_pos hf)
  unfold doobWeightedMeasure Measure.tilted
  apply congrArg (fun density : α → ℝ≥0∞ => μ.withDensity density)
  funext x
  unfold doobWeightMass
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (fun y => (mul_pos hc (Real.exp_pos (f y))).le)]
  rw [integral_const_mul]
  rw [← ENNReal.ofReal_div_of_pos hMassPos]
  rw [mul_div_mul_left _ _ (ne_of_gt hc)]

local instance posteriorFiberBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorFiberBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorFiberBridgeCompact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorFiberBridgeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorFiberBridgeMeasurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorFiberBridgeBorel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorFiberBridge

/-- For every fixed context, the continuous-compatible genuine fiber measure
is exactly the posterior conditional measure.  Only the positive common
left-dependent scalar is canceled. -/
theorem continuousCompatible_eq_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    doobWeightedMeasure
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkContinuousCompatibleFiberWeight
          H N hN beta hbeta left right target) =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalMeasure
        H N hN beta hbeta left right target := by
  let logw :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiberLogWeight
      H N hN beta hbeta left right target
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N beta‖⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta left
  have hNormPos :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N beta‖ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_ge_lower
      H N hN beta hbeta).1
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (inv_pos.mpr hNormPos)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta left)
  have hExp (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Real.exp (logw g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalGroundStateRightFiberCompleteWeight
          H N hN beta hbeta left right target g := by
    dsimp [logw]
    rw [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiberLogWeight_eq_groundStateCompleteLogWeight,
      periodicHypercubicEvenSpecialUnitaryPhysicalGroundStateRightFiberCompleteLogWeight_exp_eq]
  have hWeight :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkContinuousCompatibleFiberWeight
          H N hN beta hbeta left right target =
        (fun g => ENNReal.ofReal (c * Real.exp (logw g))) := by
    funext g
    rw [hExp g]
    change
      ENNReal.ofReal
          (c *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernel
              H N beta left (Function.update right target g) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
              H N hN beta hbeta (Function.update right target g)) =
        ENNReal.ofReal
          (c *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabKernel
                H N beta left (Function.update right target g) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta (Function.update right target g)))
    congr 1
    ring
  have hInt :
      Integrable (fun g => Real.exp (logw g))
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiberLogWeight_integrable_exp
      H N hN beta hbeta left right target
  rw [hWeight]
  exact doobWeightedMeasure_ofReal_mul_exp_eq_tilted
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    logw hInt c hc

/-- The historical normalized genuine fiber law equals the continuous
posterior conditional law for Haar-a.e. left and retained off-target contexts.
The exceptional contexts are not silently removed from this statement. -/
theorem normalizedFiberMeasure_ae_eq_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaar H N,
      ∀ᵐ retained ∂periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetHaar H N target,
        ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction
              target right = retained →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
              H N hN beta hbeta left right target =
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalMeasure
              H N hN beta hbeta left right target := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_ae_eq_continuousCompatible
      H N hN beta hbeta target] with left hLeft
  filter_upwards [hLeft] with retained hRetained
  intro right hOff
  exact (hRetained right hOff).trans
    (continuousCompatible_eq_posterior H N hN beta hbeta left right target)

/-- On the same full-measure contexts, integration against the historical
normalized fiber is the posterior BCF conditional expectation.  The context
exceptional set is independent of the test observable. -/
theorem fiberIntegral_ae_eq_posteriorConditionalExpectation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaar H N,
      ∀ᵐ retained ∂periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetHaar H N target,
        ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction
              target right = retained →
          ∀ O : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ,
            (∫ g, O (Function.update right target g)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
                H N hN beta hbeta left right target) =
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalExpectation
                H N hN beta hbeta left target O right := by
  filter_upwards [normalizedFiberMeasure_ae_eq_posterior
    H N hN beta hbeta target] with left hLeft
  filter_upwards [hLeft] with retained hRetained
  intro right hOff O
  rw [hRetained right hOff]
  exact
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorConditionalExpectation_eq_integral_conditionalMeasure
      H N hN beta hbeta left O target right).symm

end GroundStatePosteriorFiberBridge

end

end MGAP4D.MathlibAnalytic
