import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentAdjointSynthesis

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance specialUnitaryTwoRawBoundaryMomentTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoRawBoundaryMomentCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoRawBoundaryMomentSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoRawBoundaryMomentMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoRawBoundaryMomentBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoRawBoundaryMomentNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Raw finite-Wilson formulation of the theorem-generated SU(2)
primary-plaquette Gram--Schmidt readout.

The preceding layer reduced the physical realization to the output of the
actual Wilson adjoint synthesis.  Here even that operator equality is no longer
a primitive field.  The realization input is the scalar boundary-moment
identity before packaging into `L²`:

`∫_open-half K_β(b,x) u_k(x) dx = explicitGramSchmidtBoundaryObservable_k(b)`

for boundary-Haar almost every `b`, where `u_k` is the actual bounded
continuous positive-half Wilson observable produced by the coherent physical
pullback.

The existing finite-Wilson theorem
`periodicHypercubicEvenBoundaryObservableMomentL2_eq_synthesisOperator`
then reconstructs the adjoint-synthesis equality automatically.  Thus the
remaining realization frontier is exposed as an ordinary finite-dimensional
Haar integral identity, rather than an abstract Hilbert/operator statement. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : ℕ → D.positiveTimeSubalgebra.toSubmodule
  marginalSupportEventually : ∀ k,
    ∀ᶠ n in atTop, R.marginalIndex k ⊆ R.marginalIndex n
  rawBoundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryObservable : ∀ k n,
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    let Fn := Pn.positiveTimeSubmoduleCarrierLinearMap (observable k)
    let u :=
      physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n Fn
    (fun b =>
      periodicHypercubicEvenBoundaryObservableMoment
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) u b) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        (halfExtent n) k
  primaryPlaquetteGramSchmidtMode_continuum : ∀ k n
      (_h : R.marginalIndex k ⊆ R.marginalIndex n),
    L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The raw scalar boundary-moment identity theorem-generates the actual Wilson
adjoint-synthesis realization from the exact finite-Wilson adjoint theorem. -/
theorem actualSynthesis_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    let Fn := Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k)
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n Fn) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        (halfExtent n) k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let Fn := Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k)
  let u :=
    physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n Fn
  let m := periodicHypercubicEvenBoundaryObservableMomentL2
    (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n) u
  have hSynthesis :
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta n
          (Q.positiveHalfL2LinearMap hInvariant n Fn) = m := by
    rw [Q.positiveHalfL2LinearMap_apply]
    change
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)
          (periodicHypercubicEvenWilsonOpenHalfObservableL2
            (halfExtent n) 2 u) = m
    exact
      (periodicHypercubicEvenBoundaryObservableMomentL2_eq_synthesisOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) u).symm
  change
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n Fn) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        (halfExtent n) k
  rw [hSynthesis]
  exact
    (periodicHypercubicEvenBoundaryObservableMomentL2_coeFn
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) u).trans
      (C.rawBoundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryObservable k n)

/-- Forget only the raw-integral normalization.  The actual-synthesis readout is
reconstructed without any additional assumption. -/
noncomputable def toActualSynthesisReadoutData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant where
  observable := C.observable
  marginalSupportEventually := C.marginalSupportEventually
  actualSynthesis_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable :=
    C.actualSynthesis_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable
  primaryPlaquetteGramSchmidtMode_continuum :=
    C.primaryPlaquetteGramSchmidtMode_continuum

/-- The raw finite-Wilson boundary-moment package generates the canonical SU(2)
Gram--Schmidt cylinder realization. -/
noncomputable def toPrimaryPlaquetteGramSchmidtCylinderData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant :=
  C.toActualSynthesisReadoutData.toPrimaryPlaquetteGramSchmidtCylinderData

/-- Consequently the finite boundary-Haar orthonormal realization follows from
the raw Wilson Haar-integral identity. -/
noncomputable def toFiniteProjectiveCylinderBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toActualSynthesisReadoutData.toFiniteProjectiveCylinderBoundaryHaarOrthonormalData

/-- Common finite-projective-marginal orthonormality follows as well. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toActualSynthesisReadoutData.toFiniteProjectiveCylinderOrthonormalData

/-- Terminal consequence: strict continuum finite-Gram positivity on the
physical carrier is reduced to a raw finite-Wilson boundary Haar-integral
realization, continuum cylinder coherence, and eventual marginal support. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant) :=
  C.toActualSynthesisReadoutData.toFiniteOSGramPosDefPhysicalCarrierData

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtRawBoundaryMomentReadoutData

end

end MathlibAnalytic
end MGAP4D
