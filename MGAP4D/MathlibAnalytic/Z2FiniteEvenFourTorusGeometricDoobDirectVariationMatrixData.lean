import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectVariationProfiles
import MGAP4D.MathlibAnalytic.FiniteProductDoobParallelVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A lightweight generic one-coordinate variation-profile bound.  Keeping
this proposition independent of any model-specific dependent parameters makes
canonical-variation projection inexpensive to elaborate. -/
def FiniteProductVariationProfileBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    (f : (ι → G) → ℝ)
    (profile : ι → ℝ) : Prop :=
  ∀ (source : ι) (left right : ι → G),
    FiniteProductAgreeOff left right source →
      |f left - f right| ≤ profile source

/-- A nonnegative profile satisfying the one-coordinate bound controls the
canonical finite-product variation. -/
theorem FiniteProductVariationProfileBound.canonicalVariation_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [DecidableEq G]
    [Fintype G]
    {f : (ι → G) → ℝ}
    {profile : ι → ℝ}
    (hBound : FiniteProductVariationProfileBound f profile)
    (hNonneg : ∀ source : ι, 0 ≤ profile source)
    (source : ι) :
    finiteProductCanonicalVariation f source ≤ profile source := by
  let P : FiniteProductVariationBound f :=
    { variation := profile
      variation_nonneg := hNonneg
      variation_bound := hBound }
  exact finiteProductCanonicalVariation_le_variationBound P source

namespace Z2GeometricDoobDirectVariationContext

/-- The exact geometric Perron--Doob observable has the compact strict
response profile as a one-coordinate variation bound. -/
noncomputable def observableResponseProfileBound
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ) :
    FiniteProductVariationProfileBound
      (C.observable f) (C.responseProfile f) := by
  intro target left right hAgree
  let P := finiteEvenFourTorusZ2CanonicalInputVariationBound C.H f
  have hBound :=
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_difference_abs_le_observableKernelResponse_of_agreeOff
      C.continuationData C.β C.hβ C.beta_le_continuationCutoff
      C.H left right target hAgree f P
      C.envelopeKernel C.iterations
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
        C.H C.β C.energyIdentity C.energyNontrivial C.hβ C.hEnergy)
  have hBoundExpanded :
      |(finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
            C.H C.β C.energyIdentity C.energyNontrivial
            C.hβ.le C.hEnergy.le).doobObservableLinearMap f right -
          (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
            C.H C.β C.energyIdentity C.energyNontrivial
            C.hβ.le C.hEnergy.le).doobObservableLinearMap f left| ≤
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
          C.H C.β C.energyIdentity C.energyNontrivial
          (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
            C.H C.β C.energyIdentity C.energyNontrivial C.hβ C.hEnergy)
          (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
            C.energyIdentity C.energyNontrivial C.hEnergy
            C.β C.hβ C.hβCutoff C.H)
          target P.variation := by
    simpa [envelopeKernel, iterations] using hBound
  rw [finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError_eq_directResponseMatrix
    C.energyIdentity C.energyNontrivial C.hEnergy
    C.β C.hβ C.hβCutoff C.H target P.variation] at hBoundExpanded
  simpa [FiniteProductVariationProfileBound,
    observable, responseProfile, influence,
    P, finiteEvenFourTorusZ2CanonicalInputVariationBound,
    abs_sub_comm] using hBoundExpanded

/-- Proof-relevant strict variation matrix for the exact geometric Perron--Doob
observable map at one finite side. -/
noncomputable def variationMatrixData
    (C : Z2GeometricDoobDirectVariationContext) :
    FiniteProductParallelVariationMatrixData
      C.doobData.doobObservableLinearMap where
  influence := C.influence
  influence_nonneg := by
    intro target source
    exact finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_nonneg
      C.energyIdentity C.energyNontrivial C.hEnergy
      C.β C.hβ C.hβCutoff C.H target source
  canonicalVariation_le := by
    intro f target
    change finiteProductCanonicalVariation (C.observable f) target ≤
      C.responseProfile f target
    exact (C.observableResponseProfileBound f).canonicalVariation_le
      (C.responseProfile_nonneg f) target
  coefficient := 1 / 2
  coefficient_nonneg := by norm_num
  columnSum_le_coefficient := by
    intro source
    exact le_of_lt (C.influence_columnSum_lt_half source)
  coefficient_lt_one := by norm_num

/-- Direct parallel variation certificate for the exact geometric Perron--Doob
row carried by the context. -/
noncomputable def parallelVariationCertificate
    (C : Z2GeometricDoobDirectVariationContext) :
    FiniteProductDoobParallelVariationCertificate C.doobData where
  variationData := C.variationMatrixData

@[simp] theorem variationMatrixData_coefficient
    (C : Z2GeometricDoobDirectVariationContext) :
    C.variationMatrixData.coefficient = 1 / 2 := rfl

end Z2GeometricDoobDirectVariationContext

end

end MathlibAnalytic
end MGAP4D
