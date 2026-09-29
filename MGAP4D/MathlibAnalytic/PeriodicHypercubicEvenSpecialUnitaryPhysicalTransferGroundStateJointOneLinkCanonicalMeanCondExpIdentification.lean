import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCanonicalFiberMeanResidualL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

/-!
# The canonical fiber mean is the genuine joint conditional expectation

The canonical mean is already bounded and measurable on the retained outer
context, and its residual energy is no greater than the genuine CondExpL2
residual energy. These two facts identify the mean, not just its norm:
Pythagoras forces the difference from the orthogonal projection to vanish.

We use the existing joint L2 carrier and canonical residual vector. No new
conditional law, source/target commutation, cutoff or comparison estimate is
introduced. This closes the canonical-mean / joint-operator step needed after
#4930. Transport from the literal fixed-boundary means to the double joint
projection remains a separate a.e. and stationary-disintegration step.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A sub-sigma-measurable candidate cannot improve on conditional expectation
unless it is that same L2 vector. The reverse residual estimate plus
Pythagoras gives uniqueness, with no finite-measure hypothesis. -/
theorem realL2_condExp_eq_of_residual_norm_sq_le
    {α : Type*} {m : MeasurableSpace α} [m0 : MeasurableSpace α]
    {μ : Measure α} (hm : m ≤ m0) (f g : Lp ℝ 2 μ)
    (hg : AEStronglyMeasurable[m] (fun a => g a) μ)
    (hle : ‖f - g‖ ^ 2 ≤ ‖f - (condExpL2 (μ := μ) ℝ ℝ hm f).1‖ ^ 2) :
    (condExpL2 (μ := μ) ℝ ℝ hm f).1 = g := by
  let p : Lp ℝ 2 μ := (condExpL2 (μ := μ) ℝ ℝ hm f).1
  have hp : AEStronglyMeasurable[m] (fun a => p a) μ :=
    aestronglyMeasurable_condExpL2 hm f
  have hpg : AEStronglyMeasurable[m] (fun a => (p - g) a) μ := by
    exact (hp.sub hg).congr (Lp.coeFn_sub p g).symm
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm f (p - g) hpg
  have horth : inner ℝ (f - p) (p - g) = 0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr hi.symm
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (f - p) (p - g) horth
  have hsum : (f - p) + (p - g) = f - g := by abel
  rw [hsum] at hpyth
  change ‖f - g‖ ^ 2 ≤ ‖f - p‖ ^ 2 at hle
  have hzero : ‖p - g‖ = 0 := by
    nlinarith [norm_nonneg (p - g)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStateCanonicalMean

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Joint" => Cfg × Cfg
local notation "μJ" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure H N hN beta hbeta
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta

/-- Pull back the already-defined canonical outer-context mean. This is a
concrete function on the existing joint space, not a new measure or carrier. -/
def canonicalMean (target : Link) (F : Joint → ℝ) (z : Joint) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean
    H N hN beta hbeta target F
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target z)

theorem canonicalMean_stronglyMeasurable (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable (canonicalMean H N hN beta hbeta target F) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_stronglyMeasurable
    H N hN beta hbeta target F hF).comp_measurable
    (measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target)

/-- In particular the mean is measurable for the retained sub-sigma-algebra,
not merely for the ambient sigma-algebra. -/
theorem canonicalMean_stronglyMeasurable_retained (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F) :
    StronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N target]
      (canonicalMean H N hN beta hbeta target F) := by
  have hOuter : @Measurable Joint
      (PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext H N target)
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N target)
      inferInstance
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target) := by
    rw [periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_outerContextMap]
    intro s hs
    exact ⟨s, hs, rfl⟩
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_stronglyMeasurable
      H N hN beta hbeta target F hF).comp_measurable hOuter

theorem canonicalMean_norm_le (target : Link) (F : Joint → ℝ)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (z : Joint) :
    ‖canonicalMean H N hN beta hbeta target F z‖ ≤ bound :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMean_norm_le_of_bounded
    H N hN beta hbeta target F bound hbound
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap H N target z)

/-- The canonical bounded mean represents exactly the genuine CondExpL2.
Only existing boundedness and the reverse residual estimate are used. -/
theorem canonicalMeanL2_eq_condExpL2 (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta (canonicalMean H N hN beta hbeta target F)
      (canonicalMean_stronglyMeasurable H N hN beta hbeta target F hF) bound
      (canonicalMean_norm_le H N hN beta hbeta target F bound hbound) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound) := by
  let f := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta F hF bound hbound
  let M := canonicalMean H N hN beta hbeta target F
  let hM := canonicalMean_stronglyMeasurable H N hN beta hbeta target F hF
  let hMb := canonicalMean_norm_le H N hN beta hbeta target F bound hbound
  let q := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta M hM bound hMb
  let r := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
    H N hN beta hbeta target F hF bound hbound
  have hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le H N target
  have hf : (fun z => f z) =ᵐ[μJ] F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta F hF bound hbound
  have hq : (fun z => q z) =ᵐ[μJ] M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta M hM bound hMb
  have hr :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_coeFn
      H N hN beta hbeta target F hF bound hbound
  have hsub : f - q = r := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub f q, hf, hq, hr] with z hs hfz hqz hrz
    rw [hs]
    change f z - q z = r z
    rw [hfz, hqz, hrz]
    rfl
  have hqm : AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace H N target]
      (fun z => q z) μJ :=
    (canonicalMean_stronglyMeasurable_retained H N hN beta hbeta target F hF).aestronglyMeasurable.congr hq.symm
  have hEN :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_norm_sq_ofReal_le_condExpL2_residual_norm_sq_ofReal
      H N hN beta hbeta target F hF bound hbound
  have hReal : ‖r‖ ^ 2 ≤
      ‖f - (condExpL2 (μ := μJ) ℝ ℝ hm f).1‖ ^ 2 := by
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hEN
  have hle : ‖f - q‖ ^ 2 ≤
      ‖f - (condExpL2 (μ := μJ) ℝ ℝ hm f).1‖ ^ 2 := by
    rw [hsub]
    exact hReal
  exact (realL2_condExp_eq_of_residual_norm_sq_le hm f q hqm hle).symm

/-- A bounded concrete canonical mean is an explicit a.e. representative of
its genuine joint conditional expectation. -/
theorem condExpL2_coeFn_eq_canonicalMean (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound) z) =ᵐ[μJ]
    canonicalMean H N hN beta hbeta target F := by
  rw [← canonicalMeanL2_eq_condExpL2 H N hN beta hbeta target F hF bound hbound]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
    H N hN beta hbeta (canonicalMean H N hN beta hbeta target F)
    (canonicalMean_stronglyMeasurable H N hN beta hbeta target F hF) bound
    (canonicalMean_norm_le H N hN beta hbeta target F bound hbound)

/-- The pre-existing canonical residual vector is exactly f - P_target f,
not merely bounded by it in norm. -/
theorem canonicalResidualL2_eq_condExpResidual (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
      H N hN beta hbeta target F hF bound hbound =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound) := by
  let f := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    H N hN beta hbeta F hF bound hbound
  let p := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
    H N hN beta hbeta target f
  apply Lp.ext
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_coeFn
      H N hN beta hbeta target F hF bound hbound,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
      H N hN beta hbeta F hF bound hbound,
    condExpL2_coeFn_eq_canonicalMean H N hN beta hbeta target F hF bound hbound,
    Lp.coeFn_sub f p] with z hr hf hp hs
  rw [hs]
  change _ = f z - p z
  rw [hr, hf, hp]
  rfl

/-- Exact canonical fiber variance / genuine joint projection-defect identity.
Valid for all beta >= 0 on the bounded concrete core. -/
theorem canonicalVariance_eq_condExpResidualNormSq (target : Link)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
      H N hN beta hbeta target F =
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_norm_sq_ofReal_eq_variance
    H N hN beta hbeta target F hF bound hbound,
    canonicalResidualL2_eq_condExpResidual H N hN beta hbeta target F hF bound hbound]

end GroundStateCanonicalMean

end

end MGAP4D.MathlibAnalytic
