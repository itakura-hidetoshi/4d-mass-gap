import MGAP4D.MathlibAnalytic.WightmanOSPVMBoundedBorelMultiplicativity
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPVMSemigroupOSSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

/-- The positive-energy Euclidean semigroup multiplier.  Restriction to the
nonnegative spectral half-line makes the exponential globally bounded. -/
noncomputable def pvmPositiveEuclideanSemigroupMultiplier
    (t : ℝ) (ht : 0 ≤ t) : PVMBoundedBorelRealFunction where
  toFun := fun energy =>
    if 0 ≤ energy then Real.exp (-energy * t) else 0
  measurable_toFun := by
    have hExp : Measurable (fun energy : ℝ => Real.exp (-energy * t)) := by
      fun_prop
    exact Measurable.ite measurableSet_Ici hExp measurable_const
  bounded_toFun := by
    refine ⟨1, ?_⟩
    intro energy
    by_cases henergy : 0 ≤ energy
    · simp only [henergy, if_true]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith
    · simp [henergy]

@[simp] theorem pvmPositiveEuclideanSemigroupMultiplier_apply_of_nonneg
    {t energy : ℝ} (ht : 0 ≤ t) (henergy : 0 ≤ energy) :
    (pvmPositiveEuclideanSemigroupMultiplier t ht).toFun energy =
      Real.exp (-energy * t) := by
  simp [pvmPositiveEuclideanSemigroupMultiplier, henergy]

@[simp] theorem pvmPositiveEuclideanSemigroupMultiplier_apply_of_neg
    {t energy : ℝ} (ht : 0 ≤ t) (henergy : energy < 0) :
    (pvmPositiveEuclideanSemigroupMultiplier t ht).toFun energy = 0 := by
  simp [pvmPositiveEuclideanSemigroupMultiplier, not_le.mpr henergy]

/-- Positive PVM support makes the quadratic scalar spectral measure vanish on
the negative energy half-line. -/
theorem ExplicitWightmanOSPositiveSpectralSupport.scalarMeasure_Iio_zero
    {M : ExplicitWightmanOSReconstructedModel}
    (S : ExplicitWightmanOSPositiveSpectralSupport M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) :
    A.scalarMeasure ψ (Set.Iio (0 : ℝ)) = 0 := by
  rw [quadraticPVM_scalarMeasure_apply A ψ
    (Set.Iio (0 : ℝ)) measurableSet_Iio]
  rw [S.negativeProjection_zero ψ]
  simp

/-- Against the quadratic scalar measure, the positive-energy bounded multiplier
has the same integral as the full Laplace kernel because the negative half-line
is null. -/
theorem ExplicitWightmanOSPositiveSpectralSupport.integral_positiveSemigroupMultiplier_eq_laplace
    {M : ExplicitWightmanOSReconstructedModel}
    (S : ExplicitWightmanOSPositiveSpectralSupport M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (ψ : M.H) (t : ℝ) (ht : 0 ≤ t) :
    (∫ energy : ℝ,
        (pvmPositiveEuclideanSemigroupMultiplier t ht).toFun energy
        ∂(A.scalarMeasure ψ)) =
      ∫ energy : ℝ, Real.exp (-energy * t) ∂(A.scalarMeasure ψ) := by
  apply integral_congr_ae
  have hNonnegative :
      ∀ᵐ energy : ℝ ∂(A.scalarMeasure ψ),
        energy ∈ (Set.Iio (0 : ℝ))ᶜ :=
    compl_mem_ae_iff.2 (S.scalarMeasure_Iio_zero A ψ)
  filter_upwards [hNonnegative] with energy henergy
  have henergyNonneg : 0 ≤ energy := by simpa using henergy
  exact pvmPositiveEuclideanSemigroupMultiplier_apply_of_nonneg
    ht henergyNonneg

/-- A symmetric Euclidean semigroup satisfying the scalar Laplace formula is
exactly the completed PVM functional calculus of the positive-energy exponential
multiplier. -/
theorem explicitWightmanOSEuclideanTimeSemigroup_operator_eq_pvmPositiveMultiplier
    {M : ExplicitWightmanOSReconstructedModel}
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (P : ExplicitWightmanOSPositiveSpectralSupport M)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup M)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M A.toScalarSpectralRealization T)
    (t : ℝ) (ht : 0 ≤ t)
    (hSymmetric : ∀ x y : M.H,
      inner ℝ (T.operator t x) y = inner ℝ x (T.operator t y)) :
    T.operator t =
      pvmBoundedBorelSpectralIntegralOperator M.spectralPVM
        (pvmPositiveEuclideanSemigroupMultiplier t ht) := by
  apply
    continuousLinearMap_eq_pvmBoundedBorelSpectralIntegralOperator_of_inner_self_eq_integral
      A (pvmPositiveEuclideanSemigroupMultiplier t ht) (T.operator t)
  · exact hSymmetric
  · intro ψ
    calc
      inner ℝ ψ (T.operator t ψ) =
          ∫ energy : ℝ, Real.exp (-energy * t)
            ∂(A.scalarMeasure ψ) :=
        L.matrixCoefficient_eq_laplaceIntegral ψ t ht
      _ =
          ∫ energy : ℝ,
            (pvmPositiveEuclideanSemigroupMultiplier t ht).toFun energy
            ∂(A.scalarMeasure ψ) :=
        (P.integral_positiveSemigroupMultiplier_eq_laplace A ψ t ht).symm

/-- Physical OS time translation is the positive-energy exponential of the
reconstructed PVM whenever its matrix coefficients satisfy the spectral Laplace
formula and the OS exchange supplies right-time symmetry. -/
theorem EuclideanYangMillsOSPhysicalTimeTranslation.operator_eq_pvmPositiveMultiplier
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (P : ExplicitWightmanOSPositiveSpectralSupport M.toExplicitModel)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (hSymmetric : T.IsRightInnerSymmetric)
    (t : ℝ) (ht : 0 ≤ t) :
    T.operator t =
      pvmBoundedBorelSpectralIntegralOperator
        M.toExplicitModel.spectralPVM
        (pvmPositiveEuclideanSemigroupMultiplier t ht) := by
  exact explicitWightmanOSEuclideanTimeSemigroup_operator_eq_pvmPositiveMultiplier
    A P T.toEuclideanTimeSemigroup L t ht
    (hSymmetric t ht)

/-- The measure-level OS reflection/time-translation exchange identity directly
identifies the physical semigroup with the positive PVM exponential. -/
theorem EuclideanYangMillsOSPhysicalTimeTranslation.operator_eq_pvmPositiveMultiplier_of_exchange
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M.toExplicitModel)
    (P : ExplicitWightmanOSPositiveSpectralSupport M.toExplicitModel)
    (L : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      M.toExplicitModel A.toScalarSpectralRealization T.toEuclideanTimeSemigroup)
    (hExchange : T.ReflectionTimeTranslationExchange)
    (t : ℝ) (ht : 0 ≤ t) :
    T.operator t =
      pvmBoundedBorelSpectralIntegralOperator
        M.toExplicitModel.spectralPVM
        (pvmPositiveEuclideanSemigroupMultiplier t ht) := by
  exact T.operator_eq_pvmPositiveMultiplier A P L
    hExchange.toIsRightInnerSymmetric t ht

end

end MathlibAnalytic
end MGAP4D
