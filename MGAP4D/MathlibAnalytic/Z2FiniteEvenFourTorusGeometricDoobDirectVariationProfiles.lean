import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectVariationCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Short name for the exact geometric Perron--Doob observable action.  This
keeps subsequent variation theorem types small without changing the operator. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobObservable
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ) :
    FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap f

/-- Short name for one target row of the integrated strict coordinate-response
matrix acting on the canonical variation profile of an observable. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (target : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  ∑ source : FiniteEvenFourTorusSpatialLink H,
    finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff
      H target source * finiteProductCanonicalVariation f source

/-- Canonical input variation profile used in the direct geometric Doob
observable-response estimate. -/
noncomputable def finiteEvenFourTorusZ2CanonicalInputVariationBound
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ) :
    FiniteProductVariationBound f where
  variation := fun source => finiteProductCanonicalVariation f source
  variation_nonneg := finiteProductCanonicalVariation_nonneg f
  variation_bound := by
    intro source left right hAgree
    exact finiteProduct_difference_abs_le_canonicalVariation
      f source left right hAgree

/-- The direct response profile is nonnegative. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile_nonneg
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
    0 ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H f target := by
  unfold finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
  exact Finset.sum_nonneg fun source _hsource =>
    mul_nonneg
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_nonneg
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff
        H target source)
      (finiteProductCanonicalVariation_nonneg f source)

end

end MathlibAnalytic
end MGAP4D
