import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathStationarity
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

/-!
# Current finite heat-bath action on bounded continuous observables

The current compact Wilson carrier now has exact Gibbs stationarity for every
finite ordered composition of one-link heat-bath kernels.  This file turns that
finite kernel into a pointwise observable action without introducing any new
time interpretation.

For a finite ordered target list `targets`, define

`P_targets O(A) = ∫ B, O(B) d K_targets(A)`.

We record the identities needed before variation propagation:

* the empty update list acts as the identity;
* a nonempty list satisfies the exact kernel-composition recursion;
* a singleton list is the existing one-link conditional expectation;
* constants are fixed;
* the finite action preserves the canonical Wilson Gibbs mean, hence preserves
  mean-zero observables at the level of their Gibbs integral.

This remains finite-volume heat-bath kernel algebra.  Update count is not
identified with Euclidean time, and no covariance decay, continuum clustering,
positive physical mass, OS Hamiltonian gap, or uniform continuum Dobrushin
threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Pointwise action of a finite ordered list of actual one-link heat-bath
updates on a bounded continuous observable. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.finiteSingleLinkHeatBathExpectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) : ℝ :=
  ∫ B : C.base.Configuration, O B
    ∂C.finiteSingleLinkHeatBathKernel targets A

/-- A bounded continuous observable is integrable against every finite actual
heat-bath transition law. -/
theorem continuous_compact_oriented_finiteSingleLinkHeatBathObservable_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    Integrable (fun B : C.base.Configuration => O B)
      (C.finiteSingleLinkHeatBathKernel targets A) := by
  letI : IsProbabilityMeasure (C.finiteSingleLinkHeatBathKernel targets A) :=
    inferInstance
  exact
    O.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The empty finite update list acts pointwise as the identity observable. -/
@[simp] theorem continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_nil
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.finiteSingleLinkHeatBathExpectationBCF [] O A = O A := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.finiteSingleLinkHeatBathExpectationBCF]

/-- Exact observable recursion corresponding to the current finite-kernel
composition: the head target acts first. -/
theorem continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_cons
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.finiteSingleLinkHeatBathExpectationBCF (target :: targets) O A =
      ∫ B : C.base.Configuration,
        C.finiteSingleLinkHeatBathExpectationBCF targets O B
        ∂C.singleLinkHeatBathKernel target A := by
  have hInt : Integrable (fun B : C.base.Configuration => O B)
      ((C.finiteSingleLinkHeatBathKernel targets ∘ₖ
          C.singleLinkHeatBathKernel target) A) := by
    letI : IsProbabilityMeasure
        ((C.finiteSingleLinkHeatBathKernel targets ∘ₖ
          C.singleLinkHeatBathKernel target) A) := inferInstance
    exact
      O.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.finiteSingleLinkHeatBathExpectationBCF
  rw [continuous_compact_oriented_finiteSingleLinkHeatBathKernel_cons]
  simpa using
    (ProbabilityTheory.Kernel.integral_comp
      (η := C.finiteSingleLinkHeatBathKernel targets)
      (κ := C.singleLinkHeatBathKernel target)
      (a := A) hInt)

/-- A singleton finite update is exactly the existing current one-link
conditional expectation. -/
theorem continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_singleton
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration) :
    C.finiteSingleLinkHeatBathExpectationBCF [target] O A =
      C.singleLinkConditionalExpectationBCF O A target := by
  rw [continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_cons]
  simp only [continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_nil]
  exact
    continuous_compact_oriented_integral_singleLinkHeatBathKernel_BCF
      C target A O

/-- Every finite current heat-bath observable action fixes constants. -/
theorem continuous_compact_oriented_finiteSingleLinkHeatBathExpectationBCF_const
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (c : ℝ)
    (A : C.base.Configuration) :
    C.finiteSingleLinkHeatBathExpectationBCF targets
        (BoundedContinuousFunction.const _ c) A = c := by
  letI : IsProbabilityMeasure (C.finiteSingleLinkHeatBathKernel targets A) :=
    inferInstance
  simp [ContinuousCompactOrientedGaugeWilsonSystem.finiteSingleLinkHeatBathExpectationBCF]

/-- The finite current heat-bath action preserves the canonical finite-volume
Wilson Gibbs mean of every bounded continuous observable. -/
theorem continuous_compact_oriented_gibbs_integral_finiteSingleLinkHeatBathExpectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    (∫ A : C.base.Configuration,
        C.finiteSingleLinkHeatBathExpectationBCF targets O A
        ∂C.gibbsMeasure) =
      ∫ A : C.base.Configuration, O A ∂C.gibbsMeasure := by
  let K := C.finiteSingleLinkHeatBathKernel targets
  have hStationary : K ∘ₘ C.gibbsMeasure = C.gibbsMeasure := by
    simpa [K] using
      continuous_compact_oriented_finiteSingleLinkHeatBathKernel_comp_gibbsMeasure
        C targets
  have hOInt : Integrable (fun A : C.base.Configuration => O A) C.gibbsMeasure := by
    exact
      O.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hCompInt : Integrable (fun A : C.base.Configuration => O A)
      (K ∘ₘ C.gibbsMeasure) := by
    rw [hStationary]
    exact hOInt
  rw [Measure.comp_eq_comp_const_apply] at hCompInt
  have hFubini :=
    ProbabilityTheory.Kernel.integral_comp
      (η := K)
      (κ := Kernel.const Unit C.gibbsMeasure)
      (a := ()) hCompInt
  calc
    (∫ A : C.base.Configuration,
        C.finiteSingleLinkHeatBathExpectationBCF targets O A
        ∂C.gibbsMeasure) =
      ∫ A : C.base.Configuration,
        ∫ B : C.base.Configuration, O B ∂K A
        ∂C.gibbsMeasure := by
          rfl
    _ = ∫ B : C.base.Configuration, O B ∂(K ∘ₘ C.gibbsMeasure) := by
      rw [Measure.comp_eq_comp_const_apply]
      simpa [Kernel.const_apply] using hFubini.symm
    _ = ∫ A : C.base.Configuration, O A ∂C.gibbsMeasure := by
      rw [hStationary]

/-- In particular, a bounded continuous observable with zero canonical Gibbs
mean remains mean-zero after any finite ordered current heat-bath action. -/
theorem continuous_compact_oriented_gibbs_integral_finiteSingleLinkHeatBathExpectationBCF_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hO : (∫ A : C.base.Configuration, O A ∂C.gibbsMeasure) = 0) :
    (∫ A : C.base.Configuration,
        C.finiteSingleLinkHeatBathExpectationBCF targets O A
        ∂C.gibbsMeasure) = 0 := by
  rw [continuous_compact_oriented_gibbs_integral_finiteSingleLinkHeatBathExpectationBCF]
  exact hO

end

end MathlibAnalytic
end MGAP4D
