import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathCommutation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Joint continuity of ambient configuration and inserted one-link value. -/
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

/-- The exact one-link Boltzmann factor is jointly continuous in the ambient
configuration and inserted compact group value. -/
theorem continuous_compact_oriented_singleLinkBoltzmannFactor_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        C.singleLinkBoltzmannFactor z.1 target z.2) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  exact Real.continuous_exp.comp
    ((continuous_compact_oriented_gibbsExponent C).comp
      (continuous_compact_oriented_replaceLink_prod C target))

/-- The exact one-link partition function varies continuously with the ambient
configuration. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkPartitionFunction A target) := by
  let F : C.base.Configuration × C.base.Gauge → ℝ :=
    fun z => C.singleLinkBoltzmannFactor z.1 target z.2
  have hF : Continuous F := by
    simpa [F] using
      continuous_compact_oriented_singleLinkBoltzmannFactor_prod C target
  let FB : BoundedContinuousFunction
      (C.base.Configuration × C.base.Gauge) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hNorm : ∀ (A : C.base.Configuration) (g : C.base.Gauge),
      ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A g
    change ‖FB (A, g)‖ ≤ ‖FB‖
    exact FB.norm_coe_le_norm (A, g)
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
    exact Filter.Eventually.of_forall fun g => hNorm A g
  have hContinuousParameter :
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        Continuous (fun A : C.base.Configuration => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

/-- Unnormalized Boltzmann numerator for the exact one-link heat-bath transform. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathNumerator
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g : C.base.Gauge,
    C.singleLinkBoltzmannFactor A target g *
      O (C.base.replaceLink A target g)
    ∂normalizedCompactHaar C.base.Gauge

/-- The Boltzmann-weighted observable integrand is jointly continuous. -/
theorem continuous_compact_oriented_singleLinkHeatBathNumerator_integrand_prod
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous
      (fun z : C.base.Configuration × C.base.Gauge =>
        C.singleLinkBoltzmannFactor z.1 target z.2 *
          O (C.base.replaceLink z.1 target z.2)) :=
  (continuous_compact_oriented_singleLinkBoltzmannFactor_prod C target).mul
    (O.continuous.comp
      (continuous_compact_oriented_replaceLink_prod C target))

/-- The unnormalized one-link heat-bath numerator varies continuously with the
ambient compact configuration. -/
theorem continuous_compact_oriented_singleLinkHeatBathNumerator_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkHeatBathNumerator O A target) := by
  let F : C.base.Configuration × C.base.Gauge → ℝ :=
    fun z => C.singleLinkBoltzmannFactor z.1 target z.2 *
      O (C.base.replaceLink z.1 target z.2)
  have hF : Continuous F := by
    simpa [F] using
      continuous_compact_oriented_singleLinkHeatBathNumerator_integrand_prod
        C O target
  let FB : BoundedContinuousFunction
      (C.base.Configuration × C.base.Gauge) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩
  have hNorm : ∀ (A : C.base.Configuration) (g : C.base.Gauge),
      ‖F (A, g)‖ ≤ ‖FB‖ := by
    intro A g
    change ‖FB (A, g)‖ ≤ ‖FB‖
    exact FB.norm_coe_le_norm (A, g)
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
    exact Filter.Eventually.of_forall fun g => hNorm A g
  have hContinuousParameter :
      ∀ᵐ g : C.base.Gauge ∂normalizedCompactHaar C.base.Gauge,
        Continuous (fun A : C.base.Configuration => F (A, g)) :=
    Filter.Eventually.of_forall fun g =>
      hF.comp (continuous_id.prodMk continuous_const)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathNumerator
  exact continuous_of_dominated
    (bound := fun _ : C.base.Gauge => ‖FB‖)
    hMeas hBound (integrable_const ‖FB‖) hContinuousParameter

/-- The normalized exact one-link heat-bath transform is the quotient of the
continuous Boltzmann numerator by the positive one-link partition function. -/
theorem continuous_compact_oriented_singleLinkHeatBathTransform_eq_numerator_div_partition
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkHeatBathTransform target O A =
      C.singleLinkHeatBathNumerator O A target /
        C.singleLinkPartitionFunction A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransform
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  rw [MeasureTheory.integral_tilted]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathNumerator
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  simp_rw [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div]

/-- The exact one-link heat-bath transform has the Feller property on compact
continuous observables. -/
theorem continuous_compact_oriented_singleLinkHeatBathTransform_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkHeatBathTransform target O) := by
  have hNumerator :=
    continuous_compact_oriented_singleLinkHeatBathNumerator_configuration
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
      C.singleLinkHeatBathNumerator O A target /
        C.singleLinkPartitionFunction A target) :=
    hNumerator.div hPartition hPartitionNe
  have hEq :
      C.singleLinkHeatBathTransform target O =
        fun A : C.base.Configuration =>
          C.singleLinkHeatBathNumerator O A target /
            C.singleLinkPartitionFunction A target := by
    funext A
    exact
      continuous_compact_oriented_singleLinkHeatBathTransform_eq_numerator_div_partition
        C O A target
  rw [hEq]
  exact hQuotient

/-- Exact one-link heat-bath transform as a bounded continuous observable.
Compactness supplies boundedness once Feller continuity is established. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathTransformBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨C.singleLinkHeatBathTransform target O,
      continuous_compact_oriented_singleLinkHeatBathTransform_configuration
        C O target⟩

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathTransformBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathTransformBCF target O A =
      C.singleLinkHeatBathTransform target O A := by
  rfl

/-- Pairwise same-color commutation on the bounded-continuous Feller carrier. -/
theorem periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathTransformBCF_commute_of_sameColor
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    {target source : PeriodicHypercubicEvenEdge H}
    (hNe : source ≠ target)
    (hColor :
      periodicHypercubicEvenEdgeColor H target =
        periodicHypercubicEvenEdgeColor H source) :
    let C := periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
    C.singleLinkHeatBathTransformBCF source
        (C.singleLinkHeatBathTransformBCF target O) =
      C.singleLinkHeatBathTransformBCF target
        (C.singleLinkHeatBathTransformBCF source O) := by
  dsimp only
  ext A
  change
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
        source
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
            target O) A =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
          target
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hBeta).singleLinkHeatBathTransform
              source O) A
  exact congrFun
    (periodicHypercubicEvenSpecialUnitary_singleLinkHeatBathTransform_commute_of_sameColor
      H N hN beta hBeta O O.continuous hNe hColor) A

end
end MathlibAnalytic
end MGAP4D
