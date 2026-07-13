import MGAP4D.MathlibAnalytic.WightmanOSPVMSimpleQuadraticForm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- The canonical floor-grid simple approximations converge after scalar
integration to the Bochner integral of the bounded Borel multiplier against the
quadratic PVM measure. -/
theorem explicitBoundedBorelSimpleApproximation_integral_tendsto
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (F : PVMBoundedBorelRealFunction) (ψ : M.H) :
    Tendsto
      (fun n : ℕ =>
        (explicitBoundedBorelSimpleApproximation F n).integral
          (A.scalarMeasure ψ))
      atTop
      (𝓝 (∫ energy : ℝ, F.toFun energy ∂(A.scalarMeasure ψ))) := by
  letI : IsFiniteMeasure (A.scalarMeasure ψ) :=
    ⟨by
      rw [quadraticPVM_scalarMeasure_apply A ψ Set.univ MeasurableSet.univ]
      exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC⟩ := F.bounded_toFun
  have hApproxBound : ∀ (n : ℕ) (energy : ℝ),
      ‖explicitBoundedBorelSimpleApproximation F n energy‖ ≤ C + 1 := by
    intro n energy
    have hdenom : 0 < (n : ℝ) + 1 := by positivity
    have hmesh : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hdenom).2
      nlinarith
    have hError :
        ‖explicitBoundedBorelSimpleApproximation F n energy -
            F.toFun energy‖ ≤ 1 :=
      (le_of_lt
        (explicitBoundedBorelSimpleApproximation_error_lt F n energy)).trans
        hmesh
    calc
      ‖explicitBoundedBorelSimpleApproximation F n energy‖ =
          ‖F.toFun energy +
            (explicitBoundedBorelSimpleApproximation F n energy -
              F.toFun energy)‖ := by
            congr 1
            ring
      _ ≤ ‖F.toFun energy‖ +
          ‖explicitBoundedBorelSimpleApproximation F n energy -
            F.toFun energy‖ := norm_add_le _ _
      _ ≤ C + 1 := add_le_add (hC energy) hError
  have hApproxIntegrable : ∀ n : ℕ,
      Integrable
        (fun energy : ℝ =>
          explicitBoundedBorelSimpleApproximation F n energy)
        (A.scalarMeasure ψ) := by
    intro n
    exact Integrable.of_bound
      (explicitBoundedBorelSimpleApproximation F n).measurable.aestronglyMeasurable
      (C + 1)
      (Eventually.of_forall fun energy => hApproxBound n energy)
  have hPointwise : ∀ energy : ℝ,
      Tendsto
        (fun n : ℕ => explicitBoundedBorelSimpleApproximation F n energy)
        atTop (𝓝 (F.toFun energy)) := by
    intro energy
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hRate :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hEventually :
        ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_order.1 hRate).2 ε hε
    rcases eventually_atTop.1 hEventually with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    simpa [dist_eq_norm] using
      (explicitBoundedBorelSimpleApproximation_error_lt F n energy).trans
        (hN n hn)
  have hBochner :
      Tendsto
        (fun n : ℕ =>
          ∫ energy : ℝ,
            explicitBoundedBorelSimpleApproximation F n energy
              ∂(A.scalarMeasure ψ))
        atTop
        (𝓝 (∫ energy : ℝ, F.toFun energy ∂(A.scalarMeasure ψ))) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall fun n =>
        (explicitBoundedBorelSimpleApproximation F n).measurable.aestronglyMeasurable
    · exact ⟨C + 1, Eventually.of_forall fun n =>
        Eventually.of_forall fun energy => hApproxBound n energy⟩
    · exact Eventually.of_forall hPointwise
  have hSimpleToBochner :
      (fun n : ℕ =>
        (explicitBoundedBorelSimpleApproximation F n).integral
          (A.scalarMeasure ψ)) =
      (fun n : ℕ =>
        ∫ energy : ℝ,
          explicitBoundedBorelSimpleApproximation F n energy
            ∂(A.scalarMeasure ψ)) := by
    funext n
    exact SimpleFunc.integral_eq_integral
      (explicitBoundedBorelSimpleApproximation F n)
      (hApproxIntegrable n)
  rw [hSimpleToBochner]
  exact hBochner

/-- The quadratic form of the completed bounded-Borel PVM integral is exactly
the Bochner integral against the quadratic scalar spectral measure. -/
theorem pvmBoundedBorelSpectralIntegralOperator_inner_self_eq_integral
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (F : PVMBoundedBorelRealFunction) (ψ : M.H) :
    inner ℝ ψ
        (pvmBoundedBorelSpectralIntegralOperator M.spectralPVM F ψ) =
      ∫ energy : ℝ, F.toFun energy ∂(A.scalarMeasure ψ) := by
  let Q := explicitBoundedBorelCanonicalSimpleUniformApproximation F
  have hVector := Q.tendsto_completedOperator_apply M.spectralPVM ψ
  have hInner :
      Tendsto
        (fun n : ℕ =>
          inner ℝ ψ
            (pvmSimpleFuncSpectralIntegralOperator
              M.spectralPVM (Q.simple n) ψ))
        atTop
        (𝓝 (inner ℝ ψ
          (pvmBoundedBorelSpectralIntegralOperator M.spectralPVM F ψ))) := by
    simpa [Q, pvmBoundedBorelSpectralIntegralOperator] using
      tendsto_const_nhds.inner hVector
  have hTerms :
      (fun n : ℕ =>
        inner ℝ ψ
          (pvmSimpleFuncSpectralIntegralOperator
            M.spectralPVM (Q.simple n) ψ)) =
      (fun n : ℕ => (Q.simple n).integral (A.scalarMeasure ψ)) := by
    funext n
    exact pvmSimpleFuncSpectralIntegralOperator_inner_self_eq_simpleFuncIntegral
      A (Q.simple n) ψ
  rw [hTerms] at hInner
  have hScalar :
      Tendsto
        (fun n : ℕ => (Q.simple n).integral (A.scalarMeasure ψ))
        atTop
        (𝓝 (∫ energy : ℝ, F.toFun energy ∂(A.scalarMeasure ψ))) := by
    simpa [Q, explicitBoundedBorelCanonicalSimpleUniformApproximation] using
      explicitBoundedBorelSimpleApproximation_integral_tendsto A F ψ
  exact tendsto_nhds_unique hInner hScalar

/-- Equivalent inner-product orientation for downstream symmetry arguments. -/
theorem pvmBoundedBorelSpectralIntegralOperator_inner_self_eq_integral'
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (F : PVMBoundedBorelRealFunction) (ψ : M.H) :
    inner ℝ
        (pvmBoundedBorelSpectralIntegralOperator M.spectralPVM F ψ) ψ =
      ∫ energy : ℝ, F.toFun energy ∂(A.scalarMeasure ψ) := by
  rw [pvmBoundedBorelSpectralIntegralOperator_inner_eq]
  exact pvmBoundedBorelSpectralIntegralOperator_inner_self_eq_integral A F ψ

/-- A symmetric bounded operator whose diagonal matrix coefficients are the
scalar spectral integrals is the completed PVM functional calculus operator. -/
theorem continuousLinearMap_eq_pvmBoundedBorelSpectralIntegralOperator_of_inner_self_eq_integral
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (F : PVMBoundedBorelRealFunction)
    (T : M.H →L[ℝ] M.H)
    (hT : ∀ x y : M.H, inner ℝ (T x) y = inner ℝ x (T y))
    (hQuadratic : ∀ ψ : M.H,
      inner ℝ ψ (T ψ) =
        ∫ energy : ℝ, F.toFun energy ∂(A.scalarMeasure ψ)) :
    T = pvmBoundedBorelSpectralIntegralOperator M.spectralPVM F := by
  apply continuousLinearMap_eq_of_inner_self_eq_of_innerSymmetric
    T (pvmBoundedBorelSpectralIntegralOperator M.spectralPVM F)
  · exact hT
  · intro x y
    exact pvmBoundedBorelSpectralIntegralOperator_inner_eq
      M.spectralPVM F x y
  · intro ψ
    rw [hQuadratic ψ,
      pvmBoundedBorelSpectralIntegralOperator_inner_self_eq_integral A F ψ]

end

end MathlibAnalytic
end MGAP4D
