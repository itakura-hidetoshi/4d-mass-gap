import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkNumeratorContinuity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Exact compact-Haar conditional expectation is the quotient of the
unnormalized Boltzmann numerator by the positive one-link partition function. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_eq_numerator_div_partition
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalExpectation O A target =
      C.singleLinkBoltzmannNumerator O A target /
        C.singleLinkPartitionFunction A target := by
  rw [continuous_compact_oriented_singleLinkConditionalExpectation_eq_integral_density]
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannNumerator
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]

/-- The exact compact one-link conditional expectation of every bounded
continuous observable is continuous in the ambient configuration. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_configuration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration =>
      C.singleLinkConditionalExpectation O A target) := by
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
        C.singleLinkConditionalExpectation O A target) =
      fun A : C.base.Configuration =>
        C.singleLinkBoltzmannNumerator O A target /
          C.singleLinkPartitionFunction A target := by
    funext A
    exact
      continuous_compact_oriented_singleLinkConditionalExpectation_eq_numerator_div_partition
        C O A target
  rw [hEq]
  exact hQuotient

/-- The exact compact one-link heat-bath projection is continuous as a function
of the ambient configuration. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkHeatBathProjection target O) := by
  exact
    continuous_compact_oriented_singleLinkConditionalExpectation_configuration
      C O target

/-- Exact compact one-link heat-bath projection as a bounded continuous
observable. Compactness supplies boundedness after continuity is established. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjectionBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    BoundedContinuousFunction C.base.Configuration ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨C.singleLinkHeatBathProjection target O,
      continuous_compact_oriented_singleLinkHeatBathProjection C O target⟩

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathProjectionBCF_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathProjectionBCF target O A =
      C.singleLinkHeatBathProjection target O A := by
  rfl

end
end MathlibAnalytic
end MGAP4D
