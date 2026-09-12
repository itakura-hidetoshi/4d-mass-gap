import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtCylinder
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyContinuousGramSchmidtClassFunction

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance specialUnitaryTwoCoherentReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoCoherentReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoCoherentReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoCoherentReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoCoherentReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoCoherentReadoutNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}

/-- The finite OS/projective isometry factors through the canonical boundary-Haar
isometry.  This exposes the exact point at which a physical OS state has to be
identified with a theorem-generated boundary Haar mode; the later density
correction and projective pullback are already canonical linear isometries. -/
theorem finiteOSMarginalLinearIsometry_eq_boundaryHaarProjectiveL2Isometry
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n) :
    R.finiteOSMarginalLinearIsometry hInvariant n phi =
      R.boundaryHaarProjectiveL2Isometry n
        (Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n phi) :=
  rfl

/-- If one represented physical state has the explicit SU(2) primary-plaquette
Gram--Schmidt boundary-Haar mode as its OS boundary moment, then its image in
the selected interacting/projective marginal is exactly the corresponding
canonical primary-plaquette projective mode.

Thus no density-correction or projective-readout equality needs to be supplied
as a separate physical assumption. -/
theorem finiteOSMarginalLinearIsometry_physicalState_eq_primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_of_boundaryMoment
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n k : ℕ)
    (O : D.positiveTimeSubalgebra.toSubmodule)
    (hBoundary :
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
          Q.toWeakStarBridge hInvariant n
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          (halfExtent n) k) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q.toWeakStarBridge hInvariant n
  have hBoundary' :
      Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
          (halfExtent n) k := by
    simpa [Pn] using hBoundary
  change
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap O)) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k
  rw [R.finiteOSMarginalLinearIsometry_eq_boundaryHaarProjectiveL2Isometry,
    hBoundary']
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- Canonical coherent-readout data for the theorem-generated SU(2) Wilson
Gram--Schmidt family.

Unlike the preceding cylinder interface, this structure has no freely chosen
`cylinderIndex` and no freely chosen `cylinderVector`.  The canonical choices
are forced to be

`cylinderIndex k = R.marginalIndex k`

and

`cylinderVector k = R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k`.

The remaining model-facing obligations are now separated into exactly two
geometric/physical statements:

* the physical OS boundary moment of the selected positive-time observable is
  the explicit primary-plaquette Gram--Schmidt boundary-Haar mode;
* these canonical primary-plaquette modes are coherent under the actual
  projective finite-marginal transitions.

Everything after those two statements is theorem-generated. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData
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
  boundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryHaarL2 : ∀ k n,
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    Q.physicalHilbertBoundaryMomentLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        (halfExtent n) k
  primaryPlaquetteGramSchmidtMode_transition : ∀ k n
      (h : R.marginalIndex k ⊆ R.marginalIndex n),
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k)

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData

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

/-- The coherent-readout package canonically generates the previous SU(2)
primary-plaquette Gram--Schmidt cylinder data.  In particular, its finite-image
compatibility is no longer a field: it follows from the OS boundary-moment
realization and the two theorem-generated isometries after it. -/
noncomputable def toPrimaryPlaquetteGramSchmidtCylinderData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant where
  observable := C.observable
  cylinderIndex := R.marginalIndex
  cylinderVector := fun k =>
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k
  supportEventually := C.marginalSupportEventually
  finiteImage_eq_transition := by
    intro k n h
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant n
    calc
      R.finiteOSMarginalLinearIsometry hInvariant n
          (Pn.physicalState
            (Pn.positiveTimeSubmoduleCarrierLinearMap (C.observable k))) =
        R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k := by
          exact
            R.finiteOSMarginalLinearIsometry_physicalState_eq_primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_of_boundaryMoment
              hInvariant n k (C.observable k)
              (C.boundaryMoment_eq_primaryPlaquetteGramSchmidtBoundaryHaarL2 k n)
      _ = EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k) :=
        C.primaryPlaquetteGramSchmidtMode_transition k n h
  primaryPlaquetteGramSchmidtMode_eq_transition := by
    intro k n h
    exact C.primaryPlaquetteGramSchmidtMode_transition k n h

/-- Hence the coherent-readout package theorem-generates the finite boundary
Haar orthonormal realization with no arbitrary cylinder-index/vector choices. -/
noncomputable def toFiniteProjectiveCylinderBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  (C.toPrimaryPlaquetteGramSchmidtCylinderData L).toFiniteProjectiveCylinderBoundaryHaarOrthonormalData

/-- The same coherent-readout package theorem-generates common finite
projective-marginal orthonormality. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant)
    (L : EuclideanYangMillsProjectiveLimitMeasure F) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  (C.toPrimaryPlaquetteGramSchmidtCylinderData L).toFiniteProjectiveCylinderOrthonormalData

/-- Terminal consequence of the coherent-readout layer: strict continuum
finite-Gram positivity on the physical carrier follows from the two remaining
canonical realization/coherence obligations, with no arbitrary cylinder
choices and no normalized-Haar orthonormal-family assumption. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData
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
  (C.toPrimaryPlaquetteGramSchmidtCylinderData L).toFiniteOSGramPosDefPhysicalCarrierData

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
