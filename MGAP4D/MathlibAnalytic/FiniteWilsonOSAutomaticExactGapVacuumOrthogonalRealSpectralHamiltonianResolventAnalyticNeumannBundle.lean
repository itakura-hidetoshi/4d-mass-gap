import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventAnalyticNeumannBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventFactorialDerivativeBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The exact distance-to-gap ball makes the finite Wilson `Ω⊥` resolvent
perturbation strictly contractive. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    ‖(mu - lambda) •
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ < 1 := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hdist

/-- Exact local inverse representation of the finite Wilson `Ω⊥` resolvent
under the normalized contraction condition. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_eq_inverse_one_sub_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal)
    (hsmall :
      ‖(mu - lambda) •
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ < 1) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu =
      Ring.inverse
          (1 - (mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_eq_inverse_one_sub_mul
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hmu hsmall

/-- Exact local inverse representation of the finite Wilson `Ω⊥` resolvent on
the full distance-to-gap ball. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu =
      Ring.inverse
          (1 - (mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hdist

/-- Exact finite ordered Neumann expansion with remainder for the finite Wilson
`Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_neumann_nth_order_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu =
      (∑ i ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ i) *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda +
      ((mu - lambda) •
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ N *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_nth_order_of_norm_sub_lt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n N hlambda hdist

/-- Real analyticity of the finite Wilson `Ω⊥` resolvent at every parameter
strictly below the exact gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_analyticAt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    AnalyticAt ℝ
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      lambda := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_analyticAt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda

/-- Neighborhood real analyticity of the finite Wilson `Ω⊥` resolvent
throughout the exact sub-gap interval. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_analyticOnNhd
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    AnalyticOnNhd ℝ
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_analyticOnNhd
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Within-set real analyticity of the finite Wilson `Ω⊥` resolvent throughout
the exact sub-gap interval. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_analyticOn
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    AnalyticOn ℝ
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
      (Set.Iio exactGapValueReal) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_analyticOn
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Analyticity, exact local inverse representation, and finite ordered Neumann
expansions for the finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventAnalyticNeumann_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    AnalyticOnNhd ℝ
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      AnalyticOn ℝ
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n)
        (Set.Iio exactGapValueReal) ∧
      ∀ {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
          (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda),
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu =
            Ring.inverse
                (1 - (mu - lambda) •
                  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) *
              finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda ∧
          ∀ N : ℕ,
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu =
              (∑ i ∈ Finset.range N,
                  ((mu - lambda) •
                    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ i) *
                finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda +
              ((mu - lambda) •
                  finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ N *
                finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolventAnalyticNeumann_package
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

end MathlibAnalytic
end MGAP4D

end
