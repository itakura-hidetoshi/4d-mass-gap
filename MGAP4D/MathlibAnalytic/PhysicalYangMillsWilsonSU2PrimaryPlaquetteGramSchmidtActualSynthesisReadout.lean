import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentSeparationCompletion

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance specialUnitaryTwoActualSynthesisReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoActualSynthesisReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoActualSynthesisReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoActualSynthesisReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoActualSynthesisReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoActualSynthesisReadoutNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- Finite-Wilson synthesis formulation of the canonical SU(2) Gram--Schmidt
readout.

The completed OS boundary moment of a represented state is already theorem-
identified with the actual Wilson adjoint synthesis `A_φ†` applied to the
coherent positive-half `L²` pullback.  Hence the remaining realization input
can be stated entirely on that finite-volume Wilson operator:

`A_φ† (positive-half pullback of O_k)`

must agree a.e. with the explicit primary-plaquette Gram--Schmidt boundary
observable.  No equality involving the completed OS Hilbert boundary map is a
primitive field here.

The projective condition is simultaneously kept in the canonical continuum
`L²` form from the preceding layer. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
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
  actualSynthesis_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable : ∀ k n,
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    let Fn := Pn.positiveTimeSubmoduleCarrierLinearMap (observable k)
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta n
        (Q.positiveHalfL2LinearMap hInvariant n Fn) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        (halfExtent n) k
  primaryPlaquetteGramSchmidtMode_continuum : ∀ k n
      (_h : R.marginalIndex k ⊆ R.marginalIndex n),
    L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData

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

/-- The actual-synthesis realization theorem-generates the pointwise completed
OS boundary realization by the exact dense-state synthesis identity. -/
theorem boundaryMoment_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant)
    (k n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        (halfExtent n) k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  let Fn := Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k)
  have hSynthesis :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState Fn) =
        physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta n
          (Q.positiveHalfL2LinearMap hInvariant n Fn) := by
    exact
      Q.physicalHilbertBoundaryMomentLinearIsometry_physicalState_eq_actualSynthesis
        hInvariant n Fn
  change
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState Fn) =ᵐ[
      periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        (halfExtent n) k
  rw [hSynthesis]
  exact C.actualSynthesis_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable k n

/-- Forget only the finite-Wilson synthesis normalization.  The preceding
continuum-coherent pointwise package is theorem-generated without any new
physical hypothesis. -/
noncomputable def toContinuumCoherentReadoutData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant where
  observable := C.observable
  marginalSupportEventually := C.marginalSupportEventually
  boundaryMoment_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable :=
    C.boundaryMoment_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable
  primaryPlaquetteGramSchmidtMode_continuum :=
    C.primaryPlaquetteGramSchmidtMode_continuum

/-- The finite-Wilson synthesis package generates the canonical SU(2)
Gram--Schmidt cylinder realization. -/
noncomputable def toPrimaryPlaquetteGramSchmidtCylinderData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant :=
  C.toContinuumCoherentReadoutData.toPrimaryPlaquetteGramSchmidtCylinderData

/-- Finite boundary-Haar orthonormal realization is generated from the actual
Wilson adjoint synthesis identity. -/
noncomputable def toFiniteProjectiveCylinderBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toContinuumCoherentReadoutData.toFiniteProjectiveCylinderBoundaryHaarOrthonormalData

/-- Common finite-projective-marginal orthonormality follows as well. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toContinuumCoherentReadoutData.toFiniteProjectiveCylinderOrthonormalData

/-- Terminal consequence: strict continuum finite-Gram positivity on the
physical carrier now consumes an actual finite-Wilson synthesis realization,
a continuum cylinder-class coherence statement, and eventual marginal support. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant) :=
  C.toContinuumCoherentReadoutData.toFiniteOSGramPosDefPhysicalCarrierData

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtActualSynthesisReadoutData

end

end MathlibAnalytic
end MGAP4D
