import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventIdentityContinuityBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventNormBundle

open Set Filter Topology
open scoped InnerProductSpace NNReal

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite Wilson `Ω⊥` real resolvent bundled below the exact gap. -/
noncomputable def finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    Set.Iio exactGapValueReal →
      D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finite_wilson_constructed_real_spectral_hamiltonianResolventFamily
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

@[simp]
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily_apply
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : Set.Iio exactGapValueReal) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily D n lambda =
      finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda :=
  rfl

/-- Two-parameter resolvent identity on the finite Wilson `Ω⊥` sector. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_eq_smul_mul
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu =
      (lambda - mu) •
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_eq_smul_mul
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hmu

/-- Exact two-parameter operator-norm control on the finite Wilson `Ω⊥` sector. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda -
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu‖ ≤
      |lambda - mu| *
        ((exactGapValueReal - lambda)⁻¹ *
          (exactGapValueReal - mu)⁻¹) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hmu

/-- `Ω⊥` resolvent identity and its exact parameter bound as one package. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventIdentity_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ}
    (hlambda : lambda < exactGapValueReal) (hmu : mu < exactGapValueReal) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda -
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu =
        (lambda - mu) •
          (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda *
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu) ∧
      ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda -
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu‖ ≤
        |lambda - mu| *
          ((exactGapValueReal - lambda)⁻¹ *
            (exactGapValueReal - mu)⁻¹) :=
  ⟨finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_eq_smul_mul
      D n hlambda hmu,
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_norm_le
      D n hlambda hmu⟩

/-- Uniform Lipschitz control away from the exact-gap threshold on `Ω⊥`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily_lipschitzOn_subGapTruncation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LipschitzOnWith (Real.toNNReal (epsilon⁻¹ * epsilon⁻¹))
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily D n)
      {lambda : Set.Iio exactGapValueReal |
        (lambda : ℝ) ≤ exactGapValueReal - epsilon} := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolventFamily_lipschitzOn_subGapTruncation
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hepsilon

/-- The finite Wilson `Ω⊥` sub-gap resolvent family is locally Lipschitz. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily_locallyLipschitz
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    LocallyLipschitz
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily D n) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolventFamily_locallyLipschitz
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The finite Wilson `Ω⊥` real resolvent is continuous in operator norm below the gap. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily_continuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    Continuous
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily D n) :=
  (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventFamily_locallyLipschitz
    D n).continuous

end

end MathlibAnalytic
end MGAP4D
