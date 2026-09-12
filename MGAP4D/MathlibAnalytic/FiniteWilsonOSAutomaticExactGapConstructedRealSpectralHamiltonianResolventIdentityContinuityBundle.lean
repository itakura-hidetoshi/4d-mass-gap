import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventIdentityContinuityBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventNormBundle

open Set Filter Topology
open scoped InnerProductSpace NNReal

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The constructed finite Wilson real resolvent bundled below the exact gap. -/
noncomputable def finite_wilson_constructed_real_spectral_hamiltonianResolventFamily
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    Set.Iio exactGapValueReal → D.StateSpace →L[ℝ] D.StateSpace :=
  fun lambda =>
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda

@[simp]
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventFamily_apply
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : Set.Iio exactGapValueReal) :
    finite_wilson_constructed_real_spectral_hamiltonianResolventFamily D n lambda =
      finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda :=
  rfl

/-- Two-parameter resolvent identity for the constructed finite Wilson Hamiltonian. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_eq_smul_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda -
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu =
      (lambda - mu) •
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_sub_eq_smul_mul
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hmu)

/-- Exact two-parameter operator-norm control for the constructed resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda -
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu‖ ≤
      |lambda - mu| *
        ((exactGapValueReal - lambda)⁻¹ *
          (exactGapValueReal - mu)⁻¹) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_sub_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hmu)

/-- Constructed resolvent identity and its exact parameter bound as one package. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventIdentity_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda -
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu =
        (lambda - mu) •
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda *
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu) ∧
      ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda -
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu‖ ≤
        |lambda - mu| *
          ((exactGapValueReal - lambda)⁻¹ *
            (exactGapValueReal - mu)⁻¹) :=
  ⟨finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_eq_smul_mul
      D n hlambda hmu,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_norm_le
      D n hlambda hmu⟩

/-- Uniform Lipschitz control away from the exact-gap threshold. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventFamily_lipschitzOn_subGapTruncation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LipschitzOnWith (Real.toNNReal (epsilon⁻¹ * epsilon⁻¹))
      (finite_wilson_constructed_real_spectral_hamiltonianResolventFamily D n)
      {lambda : Set.Iio exactGapValueReal |
        (lambda : ℝ) ≤ exactGapValueReal - epsilon} := by
  change LipschitzOnWith (Real.toNNReal (epsilon⁻¹ * epsilon⁻¹))
    (orthonormalDiagonalHamiltonianResolventFamily
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal)
    {lambda : Set.Iio exactGapValueReal |
      (lambda : ℝ) ≤ exactGapValueReal - epsilon}
  exact
    orthonormalDiagonalHamiltonianResolventFamily_lipschitzOn_subGapTruncation
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n) hepsilon

/-- The constructed sub-gap resolvent family is locally Lipschitz. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventFamily_locallyLipschitz
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    LocallyLipschitz
      (finite_wilson_constructed_real_spectral_hamiltonianResolventFamily D n) := by
  change LocallyLipschitz
    (orthonormalDiagonalHamiltonianResolventFamily
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal)
  exact
    orthonormalDiagonalHamiltonianResolventFamily_locallyLipschitz
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)

/-- The constructed real resolvent is continuous in operator norm below the gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventFamily_continuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    Continuous
      (finite_wilson_constructed_real_spectral_hamiltonianResolventFamily D n) :=
  (finite_wilson_constructed_real_spectral_hamiltonianResolventFamily_locallyLipschitz
    D n).continuous

end

end MathlibAnalytic
end MGAP4D
