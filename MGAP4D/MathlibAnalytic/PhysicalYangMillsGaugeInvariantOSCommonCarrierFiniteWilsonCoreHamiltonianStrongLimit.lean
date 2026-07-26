import MGAP4D.MathlibAnalytic.LinearPMapDomainPointOfLE
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

/-- Embedded finite Wilson selected eigenvectors represented in the canonical
right-Hamiltonian core.

The core representation is stronger than a bare graph-closed domain lift.  The
canonical inclusion of the right Hamiltonian into its graph closure constructs
the closed-domain point automatically and preserves the operator value.  Thus
the remaining compatibility input is stated directly for the actual right
Hamiltonian on its generator domain. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
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
  coreVector :
    ℕ → SpectralIndex → T.rightHamiltonianLinearPMap.domain
  coreVector_coe :
    ∀ n k,
      (coreVector n k : P.PhysicalHilbert) =
        ((realization.excitationEmbed n
            ((finiteWitness n).spectralVector (finiteIndexEquiv n k)) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
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
  coreOperatorCompatibility_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          T.rightHamiltonianLinearPMap (coreVector n k) -
            ((realization.excitationEmbed n
                (F.hamiltonian n
                  ((finiteWitness n).spectralVector
                    (finiteIndexEquiv n k))) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))
        atTop (nhds 0)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData

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

/-- The finite selected Wilson eigenvector tracked by the common spectral
index. -/
def finiteVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The same finite selected eigenvector embedded in the continuum excitation
carrier. -/
noncomputable def embeddedVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  R.realization.excitationEmbed n (R.finiteVector n k)

@[simp] theorem coreVector_coe_eq_embeddedVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (R.coreVector n k : P.PhysicalHilbert) =
      ((R.embeddedVector n k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) := by
  simpa [embeddedVector, finiteVector] using R.coreVector_coe n k

/-- The canonical graph-extension lift from the right-Hamiltonian core to the
closed ambient Hamiltonian domain. -/
noncomputable def closedAmbientVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : T.closedRightHamiltonian.domain :=
  LinearPMap.domainPointOfLE
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian
    (R.coreVector n k)

@[simp] theorem closedAmbientVector_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (R.closedAmbientVector n k : P.PhysicalHilbert) =
      (R.coreVector n k : P.PhysicalHilbert) :=
  rfl

/-- The graph-closed Hamiltonian agrees with the canonical right Hamiltonian on
the lifted core vector. -/
theorem closedAmbientVector_value
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    T.closedRightHamiltonian (R.closedAmbientVector n k) =
      T.rightHamiltonianLinearPMap (R.coreVector n k) :=
  LinearPMap.apply_domainPointOfLE
    T.rightHamiltonianLinearPMap_le_closedRightHamiltonian
    (R.coreVector n k)

/-- The automatically lifted vector in the domain of the graph-closed
Hamiltonian restricted to continuum excitations. -/
noncomputable def approximateVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain := by
  refine ⟨R.embeddedVector n k, ?_⟩
  change
    (((R.embeddedVector n k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) ∈
      T.closedRightHamiltonian.domain
  rw [← R.coreVector_coe_eq_embeddedVector n k]
  exact T.rightHamiltonianLinearPMap_le_closedRightHamiltonian.1
    (R.coreVector n k).property

@[simp] theorem approximateVector_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (R.approximateVector n k : P.VacuumOrthogonalHilbert) =
      R.embeddedVector n k :=
  rfl

/-- The right-Hamiltonian value of the core vector, regarded in the continuum
excitation carrier. -/
noncomputable def coreHamiltonianValue
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  ⟨T.rightHamiltonianLinearPMap (R.coreVector n k), by
    rw [← R.closedAmbientVector_value n k]
    exact T.closedRightHamiltonian_range_mem_vacuumOrthogonal_of_isSelfAdjoint
      hSelf (R.closedAmbientVector n k)⟩

@[simp] theorem coreHamiltonianValue_coe
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    ((R.coreHamiltonianValue n k : P.VacuumOrthogonalHilbert) :
      P.PhysicalHilbert) =
      T.rightHamiltonianLinearPMap (R.coreVector n k) :=
  rfl

/-- The restricted graph-closed Hamiltonian acting on the automatic lift is
exactly the core right-Hamiltonian value. -/
theorem restrictedHamiltonian_approximateVector
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
        (R.approximateVector n k) =
      R.coreHamiltonianValue n k := by
  apply Subtype.ext
  change
    T.closedRightHamiltonian
        (T.vacuumOrthogonalAmbientDomainPoint (R.approximateVector n k)) =
      T.rightHamiltonianLinearPMap (R.coreVector n k)
  have hDomainPoint :
      T.vacuumOrthogonalAmbientDomainPoint (R.approximateVector n k) =
        R.closedAmbientVector n k := by
    apply Subtype.ext
    exact (R.coreVector_coe_eq_embeddedVector n k).symm
  rw [hDomainPoint, R.closedAmbientVector_value]

/-- Ambient core-Hamiltonian compatibility convergence lifts to convergence in
the complete continuum excitation carrier. -/
theorem coreOperatorCompatibility_tendsto_zero_excitation
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        R.coreHamiltonianValue n k -
          R.realization.excitationEmbed n
            (F.hamiltonian n (R.finiteVector n k)))
      atTop (nhds 0) := by
  apply (IsInducing.subtypeVal.tendsto_nhds_iff).2
  simpa [finiteVector] using R.coreOperatorCompatibility_tendsto_zero k

/-- Forget the core presentation after automatically constructing the
closed-domain lifts and the restricted operator compatibility convergence. -/
noncomputable def toCommonCarrierFiniteWilsonApproximateEigenpairStrongLimitData
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap) :
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
      simpa [embeddedVector, finiteVector] using R.approximateVector_coe n k
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralVector := R.spectralVector
    approximateValue_tendsto := R.approximateValue_tendsto
    approximateVector_tendsto := by
      intro k
      simpa [embeddedVector, finiteVector] using R.embeddedVector_tendsto k
    operatorCompatibility_tendsto_zero := by
      intro k
      simpa [finiteVector, R.restrictedHamiltonian_approximateVector] using
        R.coreOperatorCompatibility_tendsto_zero_excitation k }

/-- Core-domain finite Wilson data produce the continuum closed approximate
spectral transport package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  R.toCommonCarrierFiniteWilsonApproximateEigenpairStrongLimitData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Core-domain common-carrier Wilson spectra supply continuum confluent
resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
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

/-- The same core-domain construction gives support-local continuum
positive-power jet coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData
      A hSelf F nodes orderCap)
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

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonCoreApproximateEigenpairStrongLimitData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
