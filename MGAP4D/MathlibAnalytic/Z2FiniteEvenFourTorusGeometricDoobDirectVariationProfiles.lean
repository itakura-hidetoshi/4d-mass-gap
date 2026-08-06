import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectVariationCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Short name for the exact geometric Perron--Doob observable action. -/
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

/-- A compact proof-relevant context for one finite-volume point in the direct
geometric Doob response interval.  Bundling these dependent parameters keeps
subsequent theorem types stable under elaboration. -/
structure Z2GeometricDoobDirectVariationContext where
  energyIdentity : ℝ
  energyNontrivial : ℝ
  hEnergy : energyIdentity < energyNontrivial
  β : ℝ
  hβ : 0 < β
  hβCutoff :
    β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
      energyIdentity energyNontrivial hEnergy
  H : ℕ

namespace Z2GeometricDoobDirectVariationContext

/-- Exact Doob data carried by a compact direct-variation context. -/
noncomputable def doobData
    (C : Z2GeometricDoobDirectVariationContext) :
    FiniteKernelGroundStateDoobData
      (FiniteEvenFourTorusZ2SliceConfiguration C.H) :=
  finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    C.H C.β C.energyIdentity C.energyNontrivial C.hβ.le C.hEnergy.le

/-- Actual posterior continuation data carried by the context. -/
noncomputable def continuationData
    (C : Z2GeometricDoobDirectVariationContext) :
    Z2PerronPosteriorActualHighTemperatureContinuationData
      C.energyIdentity C.energyNontrivial C.hEnergy :=
  finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
    C.energyIdentity C.energyNontrivial C.hEnergy

/-- The context lies inside the actual posterior continuation interval. -/
theorem beta_le_continuationCutoff
    (C : Z2GeometricDoobDirectVariationContext) :
    C.β ≤ C.continuationData.couplingCutoff :=
  C.hβCutoff.trans
    (finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_le_actual
      C.energyIdentity C.energyNontrivial C.hEnergy)

/-- Compact exact geometric Doob observable action. -/
noncomputable def observable
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ) :
    FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ :=
  finiteEvenFourTorusZ2GeometricDoobObservable
    C.energyIdentity C.energyNontrivial C.hEnergy C.β C.hβ C.H f

/-- Compact strict response profile. -/
noncomputable def responseProfile
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ)
    (target : FiniteEvenFourTorusSpatialLink C.H) : ℝ :=
  finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile
    C.energyIdentity C.energyNontrivial C.hEnergy
    C.β C.hβ C.hβCutoff C.H f target

/-- Compact strict response-matrix entry. -/
noncomputable def influence
    (C : Z2GeometricDoobDirectVariationContext)
    (target source : FiniteEvenFourTorusSpatialLink C.H) : ℝ :=
  finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
    C.energyIdentity C.energyNontrivial C.hEnergy
    C.β C.hβ C.hβCutoff C.H target source

/-- Canonical finite comparison depth carried by the context. -/
noncomputable def iterations
    (C : Z2GeometricDoobDirectVariationContext) : ℕ :=
  finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
    C.energyIdentity C.energyNontrivial C.hEnergy
    C.β C.hβ C.hβCutoff C.H

/-- Canonical posterior envelope kernel carried by the context. -/
noncomputable def envelopeKernel
    (C : Z2GeometricDoobDirectVariationContext) :
    FiniteNonnegativeInfluenceKernelData
      (FiniteEvenFourTorusSpatialLink C.H) :=
  finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
    C.H C.β C.energyIdentity C.energyNontrivial C.hβ C.hEnergy

/-- The compact response profile is nonnegative. -/
theorem responseProfile_nonneg
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ)
    (target : FiniteEvenFourTorusSpatialLink C.H) :
    0 ≤ C.responseProfile f target :=
  finiteEvenFourTorusZ2GeometricDoobDirectResponseProfile_nonneg
    C.energyIdentity C.energyNontrivial C.hEnergy
    C.β C.hβ C.hβCutoff C.H f target

/-- Every compact response-matrix source column has sum strictly below one
half. -/
theorem influence_columnSum_lt_half
    (C : Z2GeometricDoobDirectVariationContext)
    (source : FiniteEvenFourTorusSpatialLink C.H) :
    (∑ target : FiniteEvenFourTorusSpatialLink C.H,
      C.influence target source) < 1 / 2 := by
  simpa [influence] using
    finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_columnSum_lt_half
      C.energyIdentity C.energyNontrivial C.hEnergy
      C.β C.hβ C.hβCutoff C.H source

end Z2GeometricDoobDirectVariationContext

end

end MathlibAnalytic
end MGAP4D
