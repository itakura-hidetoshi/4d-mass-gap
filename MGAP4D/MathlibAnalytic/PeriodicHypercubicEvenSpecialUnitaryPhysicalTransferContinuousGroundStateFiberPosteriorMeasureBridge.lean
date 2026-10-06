import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberAEBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorVariationPropagation
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic

/-!
# Genuine ground-state fibers and posterior conditional laws

The historical genuine joint fiber measure uses an L2 vacuum representative.
The posterior conditional law uses the positive continuous representative.
PR #5151 already identifies their unnormalized fiber weights for Haar-a.e.
left and off-target contexts, but retains a positive left-dependent scalar.

A positive scalar c cancels from the normalized weight c * exp(f).  Here

  c(left) = ||T_phys||^(-1) * Omega_cont(left) > 0.

We identify the continuous-compatible fiber measure with the posterior
conditional law pointwise, then use the historical a.e. bridge to identify
genuine fiber integration with the posterior BCF conditional expectation.
The full-measure contexts are independent of the BCF test.

No equality on exceptional fixed fibers, joint-L2 operator identification,
stagewise oscillation tail, physicality/commutation bound, or Euclidean-time
identification is asserted.  The strict-interval scaling no-go is unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A positive scalar cancels in a normalized exponential weight. -/
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
  change
    ENNReal.ofReal (c * Real.exp (f x)) /
        (∫⁻ y, ENNReal.ofReal (c * Real.exp (f y)) ∂μ) =
      ENNReal.ofReal (Real.exp (f x) / ∫ y, Real.exp (f y) ∂μ)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun y => (mul_pos hc (Real.exp_pos (f y))).le)]
  rw [integral_const_mul]
  rw [← ENNReal.ofReal_div_of_pos
    (x := c * Real.exp (f x)) (y := c * ∫ y, Real.exp (f y) ∂μ) hMassPos]
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

/-- Cancel the positive left-dependent scalar in every continuous context. -/
theorem continuousCompatible_eq_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    doobWeightedMeasure
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
          H N hN beta hbeta left right target) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        H N hN beta hbeta left right target := by
  let logw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
      H N hN beta hbeta left right target
  let c : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta left
  have hNormPos :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos_from_uniform_kernel_floor
      H N hN beta hbeta
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (inv_pos.mpr hNormPos)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta left)
  have hExp (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Real.exp (logw g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteWeight
          H N hN beta hbeta left right target g := by
    dsimp [logw]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_eq_groundStateCompleteLogWeight,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompleteLogWeight_exp]
  have hWeight :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousGroundStateSpatialLinkCompatibleFiberWeight
          H N hN beta hbeta left right target =
        (fun g => ENNReal.ofReal (c * Real.exp (logw g))) := by
    funext g
    rw [hExp g]
    change
      ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖⁻¹ *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta left *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta left (Function.update right target g) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta (Function.update right target g))) =
        ENNReal.ofReal
          (c *
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta left (Function.update right target g) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
                H N hN beta hbeta (Function.update right target g)))
    dsimp [c]
    congr 1
    ring
  have hLog : Continuous logw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H N hN beta hbeta left right target
  have hInt :
      Integrable (fun g => Real.exp (logw g))
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    (Real.continuous_exp.comp hLog).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [hWeight]
  exact doobWeightedMeasure_ofReal_mul_exp_eq_tilted
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    logw hInt c hc

/-- Historical genuine fibers equal posterior conditionals on a common
Haar-a.e. left/off-target context set, independently of the test observable. -/
theorem normalizedFiberMeasure_ae_eq_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N,
      ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = retained →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
              H N hN beta hbeta left right target =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
              H N hN beta hbeta left right target := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure_ae_eq_continuousCompatible
      H N hN beta hbeta target] with left hLeft
  filter_upwards [hLeft] with retained hRetained
  intro right hOff
  exact (hRetained right hOff).trans
    (continuousCompatible_eq_posterior H N hN beta hbeta left right target)

/-- Genuine fiber integration is the posterior BCF conditional expectation on
the same full-measure contexts, for every bounded-continuous test. -/
theorem fiberIntegral_ae_eq_posteriorConditionalExpectation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N,
      ∀ᵐ retained ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        ∀ right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          periodicHypercubicEvenSpatialSliceOffTargetRestriction target right = retained →
          ∀ O : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ,
            (∫ g, O (Function.update right target g)
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkNormalizedFiberMeasure
                H N hN beta hbeta left right target) =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
                H N hN beta hbeta left O right target := by
  filter_upwards [normalizedFiberMeasure_ae_eq_posterior
    H N hN beta hbeta target] with left hLeft
  filter_upwards [hLeft] with retained hRetained
  intro right hOff O
  rw [hRetained right hOff]
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_integral
      H N hN beta hbeta left O right target).symm

end GroundStatePosteriorFiberBridge

end

end MGAP4D.MathlibAnalytic
