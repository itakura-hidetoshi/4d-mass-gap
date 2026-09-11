import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtCoherentReadout
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyGramSchmidtBoundaryRepresentative

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance specialUnitaryTwoPointwiseReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoPointwiseReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoPointwiseReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoPointwiseReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoPointwiseReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoPointwiseReadoutNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Pointwise version of the canonical SU(2) Gram--Schmidt coherent readout.

The previous coherent-readout layer still stated its physical realization input
as equality with an `L²` equivalence class.  The boundary-representative theorem
now lets the model-facing statement be made directly against the explicit
continuous Wilson class-function observable.

Thus the physical input is the concrete a.e. identity

`boundary moment = explicit primary-plaquette Gram--Schmidt boundary observable`

under the actual boundary Haar measure.  Equality with the theorem-generated
`L²` mode is derived below by `Lp.ext`; it is no longer an input field. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : ℕ → D.positiveTimeSubalgebra.toSubmodule
  marginalSupportEventually : ∀ k,
    ∀ᶠ n in atTop, R.marginalIndex k ⊆ R.marginalIndex n
  boundaryMoment_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable : ∀ k n,
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        (halfExtent n) k
  primaryPlaquetteGramSchmidtMode_transition : ∀ k n
      (h : R.marginalIndex k ⊆ R.marginalIndex n),
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k)

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData

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
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The pointwise physical realization theorem-generates the previous `L²`
boundary-mode equality.  The proof is precisely extensionality of `Lp`, with
the explicit continuous observable as the common a.e. representative. -/
theorem boundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryHaarL2
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (k n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        (halfExtent n) k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  change
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        (halfExtent n) k
  apply Lp.ext
  exact
    (C.boundaryMoment_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable k n).trans
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_coeFn
        (halfExtent n) k).symm

/-- Forget only the pointwise strengthening.  The older coherent-readout
package is generated without any additional physical or measure-theoretic
assumption. -/
noncomputable def toCoherentReadoutData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant where
  observable := C.observable
  marginalSupportEventually := C.marginalSupportEventually
  boundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryHaarL2 :=
    C.boundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryHaarL2
  primaryPlaquetteGramSchmidtMode_transition :=
    C.primaryPlaquetteGramSchmidtMode_transition

/-- The pointwise coherent-readout package canonically generates the previous
SU(2) primary-plaquette Gram--Schmidt cylinder data. -/
noncomputable def toPrimaryPlaquetteGramSchmidtCylinderData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant :=
  C.toCoherentReadoutData.toPrimaryPlaquetteGramSchmidtCylinderData L

/-- Consequently finite boundary-Haar orthonormal realization is generated from
the explicit pointwise Wilson observable identity. -/
noncomputable def toFiniteProjectiveCylinderBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toCoherentReadoutData.toFiniteProjectiveCylinderBoundaryHaarOrthonormalData L

/-- The same pointwise package generates common finite-projective-marginal
orthonormality. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toCoherentReadoutData.toFiniteProjectiveCylinderOrthonormalData L

/-- Terminal consequence: strict continuum finite-Gram positivity on the
physical carrier now follows from an explicit a.e. Wilson-observable
realization plus the canonical marginal nesting/coherence data. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant) :=
  C.toCoherentReadoutData.toFiniteOSGramPosDefPhysicalCarrierData L

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
