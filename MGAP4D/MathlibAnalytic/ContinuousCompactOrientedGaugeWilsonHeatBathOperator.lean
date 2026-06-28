import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkDensity
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- A bounded continuous observable pulled back to one compact link is
integrable against the exact conditional Haar--Gibbs law. -/
theorem continuous_compact_oriented_singleLinkObservable_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Integrable
      (fun g : C.base.Gauge => O (C.base.replaceLink A target g))
      (C.singleLinkConditionalMeasure A target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  exact
    (O.continuous.comp
      (continuous_compact_oriented_replaceLink C A target)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Exact compact one-link conditional expectation is additive in the
observable. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O P : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalExpectation (O + P) A target =
      C.singleLinkConditionalExpectation O A target +
        C.singleLinkConditionalExpectation P A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  change
    (∫ g : C.base.Gauge,
      O (C.base.replaceLink A target g) +
        P (C.base.replaceLink A target g)
      ∂C.singleLinkConditionalMeasure A target) =
      (∫ g : C.base.Gauge,
        O (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target) +
      ∫ g : C.base.Gauge,
        P (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target
  exact integral_add
    (continuous_compact_oriented_singleLinkObservable_integrable
      C O A target)
    (continuous_compact_oriented_singleLinkObservable_integrable
      C P A target)

/-- Exact compact one-link conditional expectation is homogeneous over the
real scalars. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_smul
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalExpectation (c • O) A target =
      c * C.singleLinkConditionalExpectation O A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  change
    (∫ g : C.base.Gauge,
      c * O (C.base.replaceLink A target g)
      ∂C.singleLinkConditionalMeasure A target) =
      c * ∫ g : C.base.Gauge,
        O (C.base.replaceLink A target g)
        ∂C.singleLinkConditionalMeasure A target
  rw [integral_const_mul]

/-- Positivity of exact compact one-link conditional expectation. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hO : ∀ B : C.base.Configuration, 0 ≤ O B) :
    0 ≤ C.singleLinkConditionalExpectation O A target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  exact integral_nonneg fun g => hO (C.base.replaceLink A target g)

/-- Exact one-link compact Haar heat-bath projection, initially regarded as a
real function on the finite physical-link configuration space. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.base.Configuration → ℝ :=
  fun A => C.singleLinkConditionalExpectation O A target

@[simp] theorem continuous_compact_oriented_singleLinkHeatBathProjection_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.singleLinkHeatBathProjection target O A =
      C.singleLinkConditionalExpectation O A target := by
  rfl

theorem continuous_compact_oriented_singleLinkHeatBathProjection_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O P : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjection target (O + P) =
      C.singleLinkHeatBathProjection target O +
        C.singleLinkHeatBathProjection target P := by
  funext A
  exact continuous_compact_oriented_singleLinkConditionalExpectation_add
    C O P A target

theorem continuous_compact_oriented_singleLinkHeatBathProjection_smul
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (c : ℝ)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.singleLinkHeatBathProjection target (c • O) =
      c • C.singleLinkHeatBathProjection target O := by
  funext A
  change C.singleLinkConditionalExpectation (c • O) A target =
    c * C.singleLinkConditionalExpectation O A target
  exact continuous_compact_oriented_singleLinkConditionalExpectation_smul
    C c O A target

theorem continuous_compact_oriented_singleLinkHeatBathProjection_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hO : ∀ A : C.base.Configuration, 0 ≤ O A) :
    ∀ A : C.base.Configuration,
      0 ≤ C.singleLinkHeatBathProjection target O A := by
  intro A
  exact continuous_compact_oriented_singleLinkConditionalExpectation_nonneg
    C O A target hO

/-- Exact random-scan average of the compact one-link Haar heat-bath
projections. -/
def ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweep
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.base.Configuration → ℝ :=
  fun A =>
    (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
      ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathProjection target O A

@[simp] theorem continuous_compact_oriented_randomScanHeatBathSweep_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.randomScanHeatBathSweep O A =
      (Fintype.card C.base.geometry.Edge : ℝ)⁻¹ *
        ∑ target : C.base.geometry.Edge,
          C.singleLinkHeatBathProjection target O A := by
  rfl

theorem continuous_compact_oriented_randomScanHeatBathSweep_add
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O P : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.randomScanHeatBathSweep (O + P) =
      C.randomScanHeatBathSweep O + C.randomScanHeatBathSweep P := by
  funext A
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweep
  simp_rw [continuous_compact_oriented_singleLinkHeatBathProjection_add,
    Pi.add_apply]
  rw [Finset.sum_add_distrib]
  ring

theorem continuous_compact_oriented_randomScanHeatBathSweep_smul
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (c : ℝ)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.randomScanHeatBathSweep (c • O) =
      c • C.randomScanHeatBathSweep O := by
  funext A
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweep
  simp_rw [continuous_compact_oriented_singleLinkHeatBathProjection_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem continuous_compact_oriented_randomScanHeatBathSweep_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hO : ∀ A : C.base.Configuration, 0 ≤ O A) :
    ∀ A : C.base.Configuration, 0 ≤ C.randomScanHeatBathSweep O A := by
  intro A
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweep
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun target _ =>
      continuous_compact_oriented_singleLinkHeatBathProjection_nonneg
        C target O hO A)

/-- A nonempty physical-link set makes the compact random-scan heat-bath sweep
fix constants exactly. -/
theorem continuous_compact_oriented_randomScanHeatBathSweep_const
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (c : ℝ) :
    C.randomScanHeatBathSweep
        (BoundedContinuousFunction.const C.base.Configuration c) =
      fun _ : C.base.Configuration => c := by
  funext A
  unfold ContinuousCompactOrientedGaugeWilsonSystem.randomScanHeatBathSweep
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkHeatBathProjection
  simp_rw [continuous_compact_oriented_singleLinkConditionalExpectation_const]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hCard : (Fintype.card C.base.geometry.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  field_simp [hCard]

end
end MathlibAnalytic
end MGAP4D
