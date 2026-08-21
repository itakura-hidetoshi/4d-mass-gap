import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Current one-link Feller closure for compact Wilson heat-bath expectations

The current compact Wilson development already has the exact one-link conditional
expectation as a pointwise real function.  This file proves, using only the
current physical-link definitions, that this function is continuous in the
ambient configuration and therefore closes back into the bounded-continuous
observable carrier.

No historical heat-bath operator layer is imported.  The proof proceeds directly
from joint continuity of physical-link replacement and of the current Wilson
Gibbs exponent, dominated convergence on the compact gauge group, and positivity
of the current one-link partition function.

This is finite-volume Feller closure only.  It does not identify heat-bath update
count with Euclidean time and does not assert covariance decay, continuum
clustering, a physical mass gap, or a uniform continuum Dobrushin threshold.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Replacing one current physical link is jointly continuous in the ambient
configuration and the inserted compact-group value. -/
theorem continuous_compact_oriented_replaceLink_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        C.base.replaceLink z.1 target z.2) := by
  classical
  apply continuous_pi
  intro e
  by_cases h : e = target
  · subst e
    simpa [CompactOrientedGaugeWilsonSystem.replaceLink] using
      (continuous_snd : Continuous
        (fun z : C.base.Configuration × C.base.Gauge => z.2))
  · simpa [CompactOrientedGaugeWilsonSystem.replaceLink, h] using
      ((continuous_apply e).comp
        (continuous_fst : Continuous
          (fun z : C.base.Configuration × C.base.Gauge => z.1)))

/-- The current one-link Boltzmann factor is jointly continuous in ambient
configuration and inserted link value. -/
theorem continuous_compact_oriented_singleLinkBoltzmann_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        Real.exp
          (C.base.gibbsExponent
            (C.base.replaceLink z.1 target z.2))) :=
  Real.continuous_exp.comp
    ((continuous_compact_oriented_gibbsExponent C).comp
      (continuous_compact_oriented_replaceLink_prod C target))

/-- The current one-link partition function varies continuously with the
ambient configuration. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkPartitionFunction A target) := by
  let F : C.base.Configuration × C.base.Gauge → ℝ :=
    fun z =>
      Real.exp
        (C.base.gibbsExponent
          (C.base.replaceLink z.1 target z.2))
  have hF : Continuous F := by
    simpa [F] using
      continuous_compact_oriented_singleLinkBoltzmann_prod C target
  let FB : BoundedContinuousFunction
      (C.base.Configuration × C.base.Gauge) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hMeas : ∀ A : C.base.Configuration,
      AEStronglyMeasurable (fun g : C.base.Gauge => F (A, g))
        (normalizedCompactHaar C.base.Gauge) := by
    intro A
    exact
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hBound : ∀ A : C.base.Configuration,
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A
    exact Filter.Eventually.of_forall fun g => FB.norm_coe_le_norm (A, g)
  have hContinuousParameter :
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        Continuous (fun A : C.base.Configuration => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

/-- Unnormalized current one-link Boltzmann numerator for a bounded continuous
observable. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannNumerator
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g : C.base.Gauge,
    Real.exp
        (C.base.gibbsExponent
          (C.base.replaceLink A target g)) *
      O (C.base.replaceLink A target g)
    ∂normalizedCompactHaar C.base.Gauge

/-- The current Boltzmann-weighted observable integrand is jointly continuous. -/
theorem continuous_compact_oriented_singleLinkBoltzmannObservable_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        Real.exp
            (C.base.gibbsExponent
              (C.base.replaceLink z.1 target z.2)) *
          O (C.base.replaceLink z.1 target z.2)) :=
  (continuous_compact_oriented_singleLinkBoltzmann_prod C target).mul
    (O.continuous.comp
      (continuous_compact_oriented_replaceLink_prod C target))

/-- The current unnormalized one-link numerator varies continuously with the
ambient configuration. -/
theorem continuous_compact_oriented_singleLinkBoltzmannNumerator_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkBoltzmannNumerator O A target) := by
  let F : C.base.Configuration × C.base.Gauge → ℝ :=
    fun z =>
      Real.exp
          (C.base.gibbsExponent
            (C.base.replaceLink z.1 target z.2)) *
        O (C.base.replaceLink z.1 target z.2)
  have hF : Continuous F := by
    simpa [F] using
      continuous_compact_oriented_singleLinkBoltzmannObservable_prod
        C O target
  let FB : BoundedContinuousFunction
      (C.base.Configuration × C.base.Gauge) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hMeas : ∀ A : C.base.Configuration,
      AEStronglyMeasurable (fun g : C.base.Gauge => F (A, g))
        (normalizedCompactHaar C.base.Gauge) := by
    intro A
    exact
      (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hBound : ∀ A : C.base.Configuration,
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A
    exact Filter.Eventually.of_forall fun g => FB.norm_coe_le_norm (A, g)
  have hContinuousParameter :
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        Continuous (fun A : C.base.Configuration => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannNumerator
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

/-- The current exact conditional expectation is its unnormalized numerator
divided by the strictly positive current one-link partition function. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationBCF_eq_numerator_div_partition
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalExpectationBCF O A target =
      C.singleLinkBoltzmannNumerator O A target /
        C.singleLinkPartitionFunction A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationBCF
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannNumerator
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  rw [integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]

/-- The current exact one-link conditional expectation is continuous in the
ambient physical-link configuration. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationBCF_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkConditionalExpectationBCF O A target) := by
  have hNumerator :=
    continuous_compact_oriented_singleLinkBoltzmannNumerator_configuration
      C O target
  have hPartition :=
    continuous_compact_oriented_singleLinkPartitionFunction_configuration
      C target
  have hPartitionNe : ∀ A : C.base.Configuration,
      C.singleLinkPartitionFunction A target ≠ 0 := fun A =>
    ne_of_gt
      (continuous_compact_oriented_singleLinkPartitionFunction_pos
        C A target)
  have hQuotient : Continuous (fun A : C.base.Configuration =>
      C.singleLinkBoltzmannNumerator O A target /
        C.singleLinkPartitionFunction A target) :=
    hNumerator.div hPartition hPartitionNe
  have hEq :
      (fun A : C.base.Configuration =>
        C.singleLinkConditionalExpectationBCF O A target) =
      fun A : C.base.Configuration =>
        C.singleLinkBoltzmannNumerator O A target /
          C.singleLinkPartitionFunction A target := by
    funext A
    exact
      continuous_compact_oriented_singleLinkConditionalExpectationBCF_eq_numerator_div_partition
        C O A target
  rw [hEq]
  exact hQuotient

/-- Feller closure of the current exact one-link conditional expectation back
into the bounded-continuous observable carrier. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationContinuousBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A => C.singleLinkConditionalExpectationBCF O A target,
      continuous_compact_oriented_singleLinkConditionalExpectationBCF_configuration
        C O target⟩

@[simp] theorem continuous_compact_oriented_singleLinkConditionalExpectationContinuousBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkConditionalExpectationContinuousBCF target O A =
      C.singleLinkConditionalExpectationBCF O A target := by
  rfl

end

end MathlibAnalytic
end MGAP4D
