import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectVariationProfiles
import MGAP4D.MathlibAnalytic.FiniteProductDoobParallelVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- For boundary configurations agreeing away from one target link, the exact
geometric Doob observable difference is bounded directly by the compact strict
response profile. -/
theorem
    finiteEvenFourTorusZ2GeometricDoobObservable_difference_abs_le_directResponseProfile_of_agreeOff
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff left right target) :
    |finiteEvenFourTorusZ2GeometricDoobObservable
          energyIdentity energyNontrivial hEnergy β hβ H f left -
        finiteEvenFourTorusZ2GeometricDoobObservable
          energyIdentity energyNontrivial hEnergy β hβ H f right| ≤
      finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff
        H f target := by
  let C :=
    finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy
  have hβActual : β ≤ C.couplingCutoff :=
    hβCutoff.trans
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_le_actual
        energyIdentity energyNontrivial hEnergy)
  let P := finiteEvenFourTorusZ2CanonicalInputVariationBound H f
  have hBound :=
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_difference_abs_le_observableKernelResponse_of_agreeOff
      C β hβ hβActual H left right target hAgree
      f P
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
        H β energyIdentity energyNontrivial hβ hEnergy)
  rw [finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError_eq_directResponseMatrix
    energyIdentity energyNontrivial hEnergy β hβ hβCutoff
    H target P.variation] at hBound
  simpa [finiteEvenFourTorusZ2GeometricDoobObservable,
    finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile,
    P, finiteEvenFourTorusZ2CanonicalInputVariationBound,
    abs_sub_comm] using hBound

/-- The compact strict response profile is a declared variation bound for the
exact geometric Perron--Doob observable output. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectOutputVariationBound
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ) :
    FiniteProductVariationBound
      (finiteEvenFourTorusZ2GeometricDoobObservable
        energyIdentity energyNontrivial hEnergy β hβ H f) where
  variation :=
    finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H f
  variation_nonneg :=
    finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile_nonneg
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H f
  variation_bound := by
    intro target left right hAgree
    exact
      finiteEvenFourTorusZ2GeometricDoobObservable_difference_abs_le_directResponseProfile_of_agreeOff
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff
        H f target left right hAgree

/-- Canonical variation of the exact geometric Doob observable map is bounded
by the compact strict response profile. -/
theorem finiteEvenFourTorusZ2GeometricDoobObservable_canonicalVariation_le_directResponseProfile
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteProductCanonicalVariation
        (finiteEvenFourTorusZ2GeometricDoobObservable
          energyIdentity energyNontrivial hEnergy β hβ H f)
        target ≤
      finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff
        H f target := by
  exact finiteProductCanonicalVariation_le_variationBound
    (finiteEvenFourTorusZ2GeometricDoobDirectOutputVariationBound
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H f)
    target

/-- Proof-relevant strict variation matrix for the exact geometric Perron--Doob
observable map at one finite side. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectVariationMatrixData
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    FiniteProductParallelVariationMatrixData
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap where
  influence :=
    finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  influence_nonneg :=
    finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_nonneg
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  canonicalVariation_le := by
    intro f target
    change
      finiteProductCanonicalVariation
          (finiteEvenFourTorusZ2GeometricDoobObservable
            energyIdentity energyNontrivial hEnergy β hβ H f)
          target ≤
        finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff
          H f target
    exact
      finiteEvenFourTorusZ2GeometricDoobObservable_canonicalVariation_le_directResponseProfile
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H f target
  coefficient := 1 / 2
  coefficient_nonneg := by norm_num
  columnSum_le_coefficient := by
    intro source
    exact le_of_lt
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_columnSum_lt_half
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H source)
  coefficient_lt_one := by norm_num

/-- Direct parallel variation certificate for the actual geometric Doob row. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectParallelVariationCertificate
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    FiniteProductDoobParallelVariationCertificate
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) where
  variationData :=
    finiteEvenFourTorusZ2GeometricDoobDirectVariationMatrixData
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H

@[simp] theorem finiteEvenFourTorusZ2GeometricDoobDirectVariationCoefficient
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    (finiteEvenFourTorusZ2GeometricDoobDirectVariationMatrixData
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H).coefficient =
      1 / 2 := rfl

end

end MathlibAnalytic
end MGAP4D
