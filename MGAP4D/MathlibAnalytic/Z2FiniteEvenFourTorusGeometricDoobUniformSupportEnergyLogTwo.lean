import MGAP4D.MathlibAnalytic.FiniteProductDoobHalfContractionTransferGap
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectUniformGap
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusAllVolumeExcitedSupportEnergy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the volume-independent direct-response interval, every strictly excited
actual finite-`Z₂` support-Hamiltonian mode has energy at least `log 2`. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirect_excitedSupportEnergy_ge_log_two
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ.le hEnergy.le) :
    Real.log 2 ≤
      finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
        H β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive := by
  have hHalf :=
    finiteEvenFourTorusZ2GeometricDoobDirect_excitedEigenvalue_le_half
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H i
  have hLog :=
    FiniteKernelGroundStateDoobData.log_two_le_neg_log_of_pos_le_half
      ((finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).eigenvalue i.1)
      i.2.1 hHalf
  simpa [finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy,
    FiniteDimensionalSymmetricPositiveContractionData.positiveSpectralEnergy,
    FiniteDimensionalSymmetricPositiveContractionData.positiveEigenvalue,
    FiniteDimensionalSymmetricPositiveContractionData.ExcitedSpectralIndex.toPositive] using hLog

/-- Every finite side has an actual excited support mode attaining the common
lower bound statement on the same volume-independent coupling interval. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirect_exists_excitedSupportEnergy_ge_log_two
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    ∃ i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le,
      Real.log 2 ≤
        finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
          H β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive := by
  let i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
      H β energyIdentity energyNontrivial hβ.le hEnergy.le :=
    Classical.choice
      (finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict_allVolume
        H β energyIdentity energyNontrivial hβ hEnergy)
  exact ⟨i,
    finiteEvenFourTorusZ2GeometricDoobDirect_excitedSupportEnergy_ge_log_two
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H i⟩

/-- Audit-visible package combining the already established actual geometric
full-transfer uniform gap with its explicit support-Hamiltonian energy floor.
The coupling cutoff is independent of the finite side parameter `H`. -/
structure Z2FiniteEvenFourTorusGeometricDoobUniformSupportEnergyLogTwoPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) where
  cutoffPositive :
    0 < finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
      energyIdentity energyNontrivial hEnergy
  excitedSectorNonempty :
    ∀ (β : ℝ), 0 < β →
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy →
      ∀ H : ℕ,
        Nonempty
          (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
            H β energyIdentity energyNontrivial
            (by assumption).le hEnergy.le)
  allExcitedEnergyGeLogTwo :
    ∀ (β : ℝ) (hβ : 0 < β),
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy →
      ∀ (H : ℕ)
        (i : FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
          H β energyIdentity energyNontrivial hβ.le hEnergy.le),
        Real.log 2 ≤
          finiteEvenFourTorusZ2UnfixedGaugePositiveSpectralEnergy
            H β energyIdentity energyNontrivial hβ.le hEnergy.le i.toPositive
  fullTransferUniformGap :
    ∀ (β : ℝ) (hβ : 0 < β),
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy →
      Z2FiniteEvenFourTorusSpatialSandwichStabilityCompletePackage
        β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the volume-independent actual support-energy receipt. -/
noncomputable def z2FiniteEvenFourTorusGeometricDoobUniformSupportEnergyLogTwoPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusGeometricDoobUniformSupportEnergyLogTwoPackage
      energyIdentity energyNontrivial hEnergy :=
  { cutoffPositive :=
      finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_pos
        energyIdentity energyNontrivial hEnergy
    excitedSectorNonempty := by
      intro β hβ hβCutoff H
      exact
        finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict_allVolume
          H β energyIdentity energyNontrivial hβ hEnergy
    allExcitedEnergyGeLogTwo := by
      intro β hβ hβCutoff H i
      exact
        finiteEvenFourTorusZ2GeometricDoobDirect_excitedSupportEnergy_ge_log_two
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H i
    fullTransferUniformGap := by
      intro β hβ hβCutoff
      exact
        finiteEvenFourTorusZ2GeometricDoobDirectUniformGapPackage
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff }

end

end MathlibAnalytic
end MGAP4D
