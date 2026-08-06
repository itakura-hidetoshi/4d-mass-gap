import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectVariationProfiles
import MGAP4D.MathlibAnalytic.FiniteProductDoobParallelVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace Z2GeometricDoobDirectVariationContext

/-- Compact proposition asserting that the exact geometric Doob observable has
the declared one-link response profile.  The large dependent inequality is
kept in the body rather than exposed as a theorem declaration type. -/
def ObservableResponseVariationBound
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ) : Prop :=
  ∀ (target : FiniteEvenFourTorusSpatialLink C.H)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration C.H),
    FiniteProductAgreeOff left right target →
      |C.observable f left - C.observable f right| ≤
        C.responseProfile f target

/-- Proof of the compact one-link response proposition. -/
noncomputable def observableResponseVariationBoundProof
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ) :
    C.ObservableResponseVariationBound f := by
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
  simpa [ObservableResponseVariationBound, observable, responseProfile,
    influence, P, finiteEvenFourTorusZ2CanonicalInputVariationBound,
    abs_sub_comm] using hBoundExpanded

/-- The compact strict response profile is a declared variation bound for the
exact geometric Perron--Doob observable output. -/
noncomputable def outputVariationBound
    (C : Z2GeometricDoobDirectVariationContext)
    (f : FiniteEvenFourTorusZ2SliceConfiguration C.H → ℝ) :
    FiniteProductVariationBound (C.observable f) where
  variation := C.responseProfile f
  variation_nonneg := C.responseProfile_nonneg f
  variation_bound := C.observableResponseVariationBoundProof f

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
    exact finiteProductCanonicalVariation_le_variationBound
      (C.outputVariationBound f) target
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
