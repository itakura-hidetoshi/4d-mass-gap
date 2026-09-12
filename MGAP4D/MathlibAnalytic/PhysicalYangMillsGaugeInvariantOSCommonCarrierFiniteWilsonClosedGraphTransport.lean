import MGAP4D.MathlibAnalytic.LinearPMapClosedExtensionGraphLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonExcitationStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Transport actual finite Wilson Hamiltonian graphs into the domain of the
closed continuum right Hamiltonian.

For every scale and selected spectral vector, an inner sequence in the
canonical right-Hamiltonian graph converges to the raw common-carrier embedded
vector and to a prescribed graph value. Closedness of the graph closure then
puts the raw embedded vector itself in the closed Hamiltonian domain and
identifies its closed-Hamiltonian value with that graph value.

The graph value need only agree asymptotically, across scales, with the embedded
finite Wilson Hamiltonian action. No membership of the raw embedded vector in
the canonical right-generator domain, no semigroup small-time estimate, and no
scaled common-carrier semigroup defect are assumed. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) where
  realization :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData
      A F
  finiteWitness :
    (n : ℕ) →
      FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
        F n
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift => sigma.1)
          nodes orderCap
  SpectralIndex : Type
  [spectralFintype : Fintype SpectralIndex]
  finiteIndexEquiv :
    ∀ n, SpectralIndex ≃ (finiteWitness n).SpectralIndex
  spectralValue : SpectralIndex → ℝ
  spectralValue_injective : Function.Injective spectralValue
  spectralVector : SpectralIndex → P.VacuumOrthogonalHilbert
  approximateValue_tendsto :
    ∀ k,
      Tendsto
        (fun n => (finiteWitness n).spectralValue (finiteIndexEquiv n k))
        atTop (nhds (spectralValue k))
  embeddedVector_tendsto :
    ∀ k,
      Tendsto
        (fun n =>
          realization.excitationEmbed n
            ((finiteWitness n).spectralVector (finiteIndexEquiv n k)))
        atTop (nhds (spectralVector k))
  graphValue : ℕ → SpectralIndex → P.PhysicalHilbert
  graphApproximation :
    ℕ → SpectralIndex → ℕ → T.rightHamiltonianLinearPMap.domain
  graphApproximation_tendsto_embedded :
    ∀ n k,
      Tendsto
        (fun m =>
          ((graphApproximation n k m : T.rightHamiltonianLinearPMap.domain) :
            P.PhysicalHilbert))
        atTop
        (nhds
          (((realization.excitationEmbed n
              ((finiteWitness n).spectralVector (finiteIndexEquiv n k)) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
  graphApproximationValue_tendsto_graphValue :
    ∀ n k,
      Tendsto
        (fun m => T.rightHamiltonianLinearPMap (graphApproximation n k m))
        atTop (nhds (graphValue n k))
  graphValueCompatibility_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          graphValue n k -
            (((realization.excitationEmbed n
                (F.hamiltonian n
                  ((finiteWitness n).spectralVector
                    (finiteIndexEquiv n k))) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
        atTop (nhds 0)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData

variable
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q}
    {hSelf : IsSelfAdjoint T.closedRightHamiltonian}
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    {nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift}
    {orderCap : ℕ}

abbrev ClosedGraphTransportData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData
    A hSelf F nodes orderCap

/-- The selected finite Wilson eigenvector. -/
def finiteVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The selected finite vector embedded in the continuum excitation carrier. -/
noncomputable def embeddedVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  R.realization.excitationEmbed n (R.finiteVector n k)

/-- The raw embedded selected vector in the ambient continuum Hilbert space. -/
noncomputable def ambientEmbeddedVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  ((R.embeddedVector n k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)

/-- The embedded finite Wilson Hamiltonian action in the ambient carrier. -/
noncomputable def ambientHamiltonianVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  (((R.realization.excitationEmbed n
        (F.hamiltonian n (R.finiteVector n k)) :
      P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))

/-- The inner canonical graph approximation converges to the named raw embedded
vector. -/
theorem graphApproximation_tendsto_ambientEmbeddedVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    Tendsto
      (fun m =>
        ((R.graphApproximation n k m : T.rightHamiltonianLinearPMap.domain) :
          P.PhysicalHilbert))
      atTop (nhds (R.ambientEmbeddedVector n k)) := by
  simpa [ambientEmbeddedVector, embeddedVector, finiteVector] using
    R.graphApproximation_tendsto_embedded n k

/-- Closed-graph transport bundles the raw embedded selected vector in the
closed continuum Hamiltonian domain. -/
noncomputable def closedAmbientVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : T.closedRightHamiltonian.domain :=
  LinearPMap.domainPointOfClosedExtensionGraphLimit
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian
    T.closedRightHamiltonian_isClosed
    (R.graphApproximation_tendsto_ambientEmbeddedVector n k)
    (R.graphApproximationValue_tendsto_graphValue n k)

@[simp] theorem closedAmbientVector_coe
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (R.closedAmbientVector n k : P.PhysicalHilbert) =
      R.ambientEmbeddedVector n k :=
  rfl

/-- The closed continuum Hamiltonian value of the transported raw vector is the
prescribed graph limit. -/
theorem closedAmbientVector_value
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    T.closedRightHamiltonian (R.closedAmbientVector n k) =
      R.graphValue n k := by
  exact LinearPMap.apply_domainPointOfClosedExtensionGraphLimit
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian
    T.closedRightHamiltonian_isClosed
    (R.graphApproximation_tendsto_ambientEmbeddedVector n k)
    (R.graphApproximationValue_tendsto_graphValue n k)

/-- The transported raw vector in the domain of the closed Hamiltonian
restricted to continuum excitations. -/
noncomputable def approximateVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain := by
  refine ⟨R.embeddedVector n k, ?_⟩
  change R.ambientEmbeddedVector n k ∈ T.closedRightHamiltonian.domain
  rw [← R.closedAmbientVector_coe n k]
  exact (R.closedAmbientVector n k).property

@[simp] theorem approximateVector_coe
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (R.approximateVector n k : P.VacuumOrthogonalHilbert) =
      R.embeddedVector n k :=
  rfl

/-- The graph-limit Hamiltonian value belongs to the continuum excitation
sector by self-adjoint invariance of the closed Hamiltonian. -/
noncomputable def closedHamiltonianValue
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  ⟨R.graphValue n k, by
    rw [← R.closedAmbientVector_value n k]
    exact T.closedRightHamiltonian_range_mem_vacuumOrthogonal_of_isSelfAdjoint
      hSelf (R.closedAmbientVector n k)⟩

@[simp] theorem closedHamiltonianValue_coe
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    ((R.closedHamiltonianValue n k : P.VacuumOrthogonalHilbert) :
      P.PhysicalHilbert) = R.graphValue n k :=
  rfl

/-- The restricted closed Hamiltonian acting on the raw embedded vector is the
transported graph-limit value. -/
theorem restrictedHamiltonian_approximateVector
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (R.approximateVector n k) =
      R.closedHamiltonianValue n k := by
  apply Subtype.ext
  change
    T.closedRightHamiltonian
        (T.vacuumOrthogonalAmbientDomainPoint (R.approximateVector n k)) =
      R.graphValue n k
  have hDomainPoint :
      T.vacuumOrthogonalAmbientDomainPoint (R.approximateVector n k) =
        R.closedAmbientVector n k := by
    apply Subtype.ext
    exact (R.closedAmbientVector_coe n k).symm
  rw [hDomainPoint, R.closedAmbientVector_value]

/-- Scale-wise asymptotic agreement of graph values with the embedded finite
Hamiltonian actions, lifted to the complete excitation carrier. -/
theorem closedHamiltonianValue_sub_embeddedHamiltonian_tendsto_zero
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        R.closedHamiltonianValue n k -
          R.realization.excitationEmbed n
            (F.hamiltonian n (R.finiteVector n k)))
      atTop (nhds 0) := by
  apply (IsInducing.subtypeVal.tendsto_nhds_iff).2
  simpa [closedHamiltonianValue, ambientHamiltonianVector, finiteVector] using
    R.graphValueCompatibility_tendsto_zero k

/-- Forget the inner graph-approximation presentation after constructing exact
closed-domain lifts of the raw embedded selected vectors. -/
noncomputable def toCommonCarrierFiniteWilsonApproximateEigenpairStrongLimitData
    (R : ClosedGraphTransportData A hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap :=
  { realization := R.realization
    finiteWitness := R.finiteWitness
    SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    finiteIndexEquiv := R.finiteIndexEquiv
    approximateVector := R.approximateVector
    approximateVector_coe := by
      intro n k
      rfl
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralVector := R.spectralVector
    approximateValue_tendsto := R.approximateValue_tendsto
    approximateVector_tendsto := by
      intro k
      simpa [approximateVector, embeddedVector, finiteVector] using
        R.embeddedVector_tendsto k
    operatorCompatibility_tendsto_zero := by
      intro k
      simpa [finiteVector, R.restrictedHamiltonian_approximateVector] using
        R.closedHamiltonianValue_sub_embeddedHamiltonian_tendsto_zero k }

/-- Closed-graph transport of actual finite Wilson vectors constructs the
continuum resolvent approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : ClosedGraphTransportData A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  R.toCommonCarrierFiniteWilsonApproximateEigenpairStrongLimitData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Closed-graph transported finite Wilson spectra supply continuum
confluent-resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift =>
            A.toVacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  R.toCommonCarrierFiniteWilsonApproximateEigenpairStrongLimitData
    |>.continuumResolventConfluentCauchy_linearIndependent hP hInnerSymmetric

/-- The same closed-graph transport gives support-local positive-power jet
coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : ClosedGraphTransportData A hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (hFit : A.toVacuumSemigroupGapSlope.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  R.toCommonCarrierFiniteWilsonApproximateEigenpairStrongLimitData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP hInnerSymmetric left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonClosedGraphTransportData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
