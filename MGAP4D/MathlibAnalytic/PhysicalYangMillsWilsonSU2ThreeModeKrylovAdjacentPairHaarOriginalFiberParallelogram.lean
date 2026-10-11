import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorQuadraticHomogeneity
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# P4-Q2-BJ: exact Haar fiber variance parallelogram on original Wilson sections

BI proves scalar quadratic homogeneity for the original Wilson right/left
all-link Haar reference. The next nontrivial quadratic-form input is the
parallelogram law, not mere homogeneity.

This file first reuses pinned mathlib variance_fun_add / variance_fun_sub
and ofReal_variance to prove the evariance parallelogram on arbitrary
finite-measure spaces for two L² inputs. It then proves the identity on
the literal ORIGINAL Wilson right one-link Haar section of two bounded
strongly measurable concrete joint observables, for every left boundary
and retained off-target context. No change to the physical measure,
fiber masses, or exp(-32 beta) factors is made.

The last lemma includes the actual nonnegative mass weighting at any
fixed context. Integrating it over the original outer Haar carrier
requires an independently justified measurability/additivity step;
the full integrated reference parallelogram is NOT yet asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1400000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

/-- Algebraic real-variance parallelogram under precisely the pinned
mathlib L² / finite-measure hypotheses. No independence is required. -/
theorem p4Q2BJ_variance_parallelogram
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun u => X u + Y u) μ +
      variance (fun u => X u - Y u) μ =
      2 * (variance X μ + variance Y μ) := by
  rw [ProbabilityTheory.variance_fun_add hX hY,
    ProbabilityTheory.variance_fun_sub hX hY]
  ring

/-- The EXACT extended-real Haar-variance parallelogram. Using MemLp
makes the ENNReal conversion legitimate, including its finite additions. -/
theorem p4Q2BJ_evariance_parallelogram
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    evariance (fun u => X u + Y u) μ +
      evariance (fun u => X u - Y u) μ =
      (2 : ENNReal) * (evariance X μ + evariance Y μ) := by
  have hreal := p4Q2BJ_variance_parallelogram μ X Y hX hY
  have hPlus :
      ENNReal.ofReal (variance (fun u => X u + Y u) μ) =
        evariance (fun u => X u + Y u) μ := by
    simpa only [Pi.add_apply] using
      (ProbabilityTheory.ofReal_variance (hX.add hY))
  have hMinus :
      ENNReal.ofReal (variance (fun u => X u - Y u) μ) =
        evariance (fun u => X u - Y u) μ := by
    simpa only [Pi.sub_apply] using
      (ProbabilityTheory.ofReal_variance (hX.sub hY))
  calc
    evariance (fun u => X u + Y u) μ +
        evariance (fun u => X u - Y u) μ =
      ENNReal.ofReal (variance (fun u => X u + Y u) μ) +
        ENNReal.ofReal (variance (fun u => X u - Y u) μ) := by
          rw [← hPlus, ← hMinus]
    _ = ENNReal.ofReal
        (variance (fun u => X u + Y u) μ +
          variance (fun u => X u - Y u) μ) := by
          rw [ENNReal.ofReal_add
            (ProbabilityTheory.variance_nonneg _ _)
            (ProbabilityTheory.variance_nonneg _ _)]
    _ = ENNReal.ofReal (2 * (variance X μ + variance Y μ)) :=
      congrArg ENNReal.ofReal hreal
    _ = (2 : ENNReal) * (evariance X μ + evariance Y μ) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_add
              (ProbabilityTheory.variance_nonneg X μ)
              (ProbabilityTheory.variance_nonneg Y μ),
            ProbabilityTheory.ofReal_variance hX,
            ProbabilityTheory.ofReal_variance hY]
          norm_num

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "SU" => Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Additivity of the actual concrete one-link section, at the same
left boundary, retained off-target coordinates, and target SU(N) link. -/
theorem p4Q2BJ_originalJointOneLinkSection_add
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F G : Joint → ℝ)
    (left : Cfg)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → SU) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target (fun z => F z + G z) left retained =
      (fun u : SU =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained u +
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target G left retained u) := by
  funext u
  rfl

/-- Subtraction in the same original Wilson concrete target-link section. -/
theorem p4Q2BJ_originalJointOneLinkSection_sub
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F G : Joint → ℝ)
    (left : Cfg)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → SU) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target (fun z => F z - G z) left retained =
      (fun u : SU =>
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained u -
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target G left retained u) := by
  funext u
  rfl

/-- Each bounded strongly measurable original joint function induces an
honest Haar-L² one-link section in EVERY fixed physical outer context.
No regular-conditional-law claim for exceptional fibers is required. -/
theorem p4Q2BJ_originalJointOneLinkSection_memLp
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : Cfg)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → SU) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retained)
      2 (normalizedCompactHaar SU) := by
  let μHaar : Measure SU := normalizedCompactHaar SU
  letI : IsProbabilityMeasure μHaar := by
    dsimp [μHaar]
    infer_instance
  have hmeas :
      StronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained) :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
      H N target F hF left retained
  have hsectionBound :
      ∀ u : SU,
        ‖periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained u‖ ≤ bound := by
    intro u
    change ‖F
        (left,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm u, retained))‖ ≤ bound
    exact hbound _
  exact MemLp.of_bound hmeas.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hsectionBound)

/-- Parallelogram in the Haar fiber of the LITERAL physical Wilson
right one-link reference. The original section's F±G retain the same
physical left boundary, retained context, and target Haar law. -/
theorem p4Q2BJ_originalJointOneLinkHaarFiber_parallelogram
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG)
    (left : Cfg)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → SU) :
    evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target (fun z => F z + G z) left retained)
        (normalizedCompactHaar SU) +
      evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target (fun z => F z - G z) left retained)
        (normalizedCompactHaar SU) =
      (2 : ENNReal) *
        (evariance
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F left retained)
          (normalizedCompactHaar SU) +
         evariance
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target G left retained)
          (normalizedCompactHaar SU)) := by
  rw [p4Q2BJ_originalJointOneLinkSection_add H N target F G left retained,
    p4Q2BJ_originalJointOneLinkSection_sub H N target F G left retained]
  exact p4Q2BJ_evariance_parallelogram
    (normalizedCompactHaar SU)
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retained)
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target G left retained)
    (p4Q2BJ_originalJointOneLinkSection_memLp
      H N target F hF boundF hboundF left retained)
    (p4Q2BJ_originalJointOneLinkSection_memLp
      H N target G hG boundG hboundG left retained)

/-- The literal Wilson original ground-state fiber mass and local
exp(-32 beta) coefficient may be retained as an arbitrary nonnegative
common context weight in the fiber parallelogram law. -/
theorem p4Q2BJ_originalJointOneLinkHaarFiber_weighted_parallelogram
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F G : Joint → ℝ)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (boundF : ℝ) (hboundF : ∀ z, ‖F z‖ ≤ boundF)
    (boundG : ℝ) (hboundG : ∀ z, ‖G z‖ ≤ boundG)
    (left : Cfg)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target → SU)
    (weight : ENNReal) :
    weight *
      evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target (fun z => F z + G z) left retained)
        (normalizedCompactHaar SU) +
    weight *
      evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target (fun z => F z - G z) left retained)
        (normalizedCompactHaar SU) =
    (2 : ENNReal) * (
      weight * evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained)
        (normalizedCompactHaar SU) +
      weight * evariance
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target G left retained)
        (normalizedCompactHaar SU)) := by
  rw [← mul_add,
    p4Q2BJ_originalJointOneLinkHaarFiber_parallelogram
      H N target F G hF hG boundF hboundF boundG hboundG left retained]
  simp only [mul_add]
  ac_rfl

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
