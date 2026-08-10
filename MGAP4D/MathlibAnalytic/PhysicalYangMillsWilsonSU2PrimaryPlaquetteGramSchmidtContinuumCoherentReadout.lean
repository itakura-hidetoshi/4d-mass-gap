import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadout
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveFiniteMarginalL2TransitionTrans

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance specialUnitaryTwoContinuumCoherentReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoContinuumCoherentReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoContinuumCoherentReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoContinuumCoherentReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoContinuumCoherentReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance specialUnitaryTwoContinuumCoherentReadoutNontrivial :
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

/-- The canonical projective transition equation for the explicit SU(2)
primary-plaquette Gram--Schmidt modes is equivalent to saying that the two
finite-marginal modes represent the same vector after embedding into the single
projective-limit continuum `L²` space.

The forward direction is exactly projective compatibility.  The reverse
direction uses injectivity of the large-marginal continuum pullback. -/
theorem primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_transition_iff_continuumPullback_eq
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (k n : ℕ)
    (h : R.marginalIndex k ⊆ R.marginalIndex n) :
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k =
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k) ↔
      L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k) =
        L.finiteMarginalL2Pullback (R.marginalIndex k)
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k) := by
  constructor
  · intro hTransition
    rw [hTransition]
    exact
      (L.finiteMarginalL2Pullback_compatible h
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k)).symm
  · intro hContinuum
    apply (L.finiteMarginalL2Pullback (R.marginalIndex n)).injective
    rw [← L.finiteMarginalL2Pullback_compatible h]
    exact hContinuum

/-- The continuum `L²` cylinder vector canonically represented by the diagonal
primary-plaquette Gram--Schmidt mode at scale `k`. -/
noncomputable def primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (k : ℕ) : Lp ℝ 2 L.continuumMeasure :=
  L.finiteMarginalL2Pullback (R.marginalIndex k)
    (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k)

/-- Transition coherence is equivalently equality with the named canonical
continuum cylinder mode. -/
theorem primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_transition_iff_continuumMode_eq
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout
      Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (k n : ℕ)
    (h : R.marginalIndex k ⊆ R.marginalIndex n) :
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k =
        EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
          (F := F) h
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode k k) ↔
      L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k) =
        R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k := by
  exact
    R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_transition_iff_continuumPullback_eq
      L k n h

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout

/-- Continuum-normalized version of the pointwise SU(2) Gram--Schmidt coherent
readout.

The finite-marginal transition equation is no longer a field.  Instead each
larger-scale primary-plaquette mode is required to represent the single named
continuum cylinder vector determined at its source scale.  The equivalence
above theorem-generates the former transition equation.

The remaining model-facing inputs are therefore expressed on the two actual
continuum-facing objects:

* an explicit a.e. boundary Wilson observable realizing the physical OS
  boundary moment;
* one continuum `L²` cylinder class shared by its finite-marginal
  representatives. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
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
  primaryPlaquetteGramSchmidtMode_continuum : ∀ k n
      (h : R.marginalIndex k ⊆ R.marginalIndex n),
    L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k) =
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k

namespace PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

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

/-- Forget only the continuum normalization of projective coherence.  The
finite transition equation is recovered by the generic compatibility/
injectivity equivalence. -/
noncomputable def toPointwiseCoherentReadoutData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtPointwiseCoherentReadoutData
      S D halfExtent beta hbeta Q F R hInvariant where
  observable := C.observable
  marginalSupportEventually := C.marginalSupportEventually
  boundaryMoment_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable :=
    C.boundaryMoment_coeFn_eq_primaryPlaquetteGramSchmidtBoundaryObservable
  primaryPlaquetteGramSchmidtMode_transition := by
    intro k n h
    exact
      (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_transition_iff_continuumMode_eq
        L k n h).2 (C.primaryPlaquetteGramSchmidtMode_continuum k n h)

/-- The continuum-coherent package canonically generates the prior cylinder
realization. -/
noncomputable def toPrimaryPlaquetteGramSchmidtCylinderData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtCylinderData
      S D halfExtent beta hbeta Q F R L hInvariant :=
  C.toPointwiseCoherentReadoutData.toPrimaryPlaquetteGramSchmidtCylinderData L

/-- Boundary-Haar orthonormality follows from the continuum-coherent pointwise
package. -/
noncomputable def toFiniteProjectiveCylinderBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toPointwiseCoherentReadoutData.toFiniteProjectiveCylinderBoundaryHaarOrthonormalData L

/-- Common finite-projective-marginal orthonormality follows as well. -/
noncomputable def toFiniteProjectiveCylinderOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderOrthonormalData
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      Q F R L hInvariant :=
  C.toPointwiseCoherentReadoutData.toFiniteProjectiveCylinderOrthonormalData L

/-- Terminal consequence: strict continuum finite-Gram positivity on the
physical carrier now consumes a pointwise boundary realization and a single
continuum cylinder-class coherence statement, rather than an ad hoc family of
finite transition equations. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
      S D halfExtent beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        Q.toWeakStarBridge hInvariant) :=
  C.toPointwiseCoherentReadoutData.toFiniteOSGramPosDefPhysicalCarrierData L

end PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData

end

end MathlibAnalytic
end MGAP4D
