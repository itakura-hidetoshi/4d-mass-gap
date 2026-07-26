import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSMovingRightHamiltonianGraphDiagonalSelection
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonTimeAverageStrongLimit
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

/-- Actual finite Wilson spectral vectors realized in the common continuum carrier,
with explicit membership in the continuum right-generator domain and asymptotic
right-Hamiltonian graph compatibility.

The shrinking widths are not inputs.  They are selected simultaneously from the
continuum right-Hamiltonian difference-quotient limits.  No finite-semigroup
exponential action and no scaled common-carrier semigroup defect are assumed. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonRightGeneratorGraphStrongLimitData
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
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
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
  ambientEmbeddedVector_mem_rightGeneratorDomain :
    ∀ n k,
      (((realization.excitationEmbed n
            ((finiteWitness n).spectralVector (finiteIndexEquiv n k)) :
          P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) ∈
        T.rightGeneratorDomain
  rightHamiltonianCompatibility_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          T.rightHamiltonian
              ⟨(((realization.excitationEmbed n
                    ((finiteWitness n).spectralVector
                      (finiteIndexEquiv n k)) :
                  P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)),
                ambientEmbeddedVector_mem_rightGeneratorDomain n k⟩ -
            (((realization.excitationEmbed n
                  (F.hamiltonian n
                    ((finiteWitness n).spectralVector
                      (finiteIndexEquiv n k))) :
                P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
        atTop (nhds 0)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonRightGeneratorGraphStrongLimitData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonRightGeneratorGraphStrongLimitData

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
    {hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric}
    {hSelf : IsSelfAdjoint T.closedRightHamiltonian}
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    {nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift}
    {orderCap : ℕ}

abbrev RightGeneratorGraphData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonRightGeneratorGraphStrongLimitData
    A hInnerSymmetric hSelf F nodes orderCap

/-- The selected finite Wilson energy. -/
def approximateValue
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The selected finite Wilson Hamiltonian eigenvector. -/
def finiteVector
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The selected finite vector embedded in the continuum excitation carrier. -/
noncomputable def embeddedVector
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  R.realization.excitationEmbed n (R.finiteVector n k)

/-- The selected embedded vector in the ambient continuum Hilbert space. -/
noncomputable def ambientEmbeddedVector
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  ((R.embeddedVector n k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)

/-- The finite Hamiltonian action embedded in the ambient continuum carrier. -/
noncomputable def ambientHamiltonianVector
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  (((R.realization.excitationEmbed n
        (F.hamiltonian n (R.finiteVector n k)) :
      P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))

/-- The selected ambient vector bundled in the continuum right-generator domain. -/
noncomputable def ambientDomainPoint
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : T.rightGeneratorDomain :=
  ⟨R.ambientEmbeddedVector n k, by
    simpa [ambientEmbeddedVector, embeddedVector, finiteVector] using
      R.ambientEmbeddedVector_mem_rightGeneratorDomain n k⟩

@[simp] theorem ambientDomainPoint_coe
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (R.ambientDomainPoint n k : P.PhysicalHilbert) =
      R.ambientEmbeddedVector n k :=
  rfl

/-- The actual Wilson graph package as an instance of the generic moving
right-Hamiltonian graph data. -/
noncomputable def toMovingRightHamiltonianGraphData
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap) :
    MovingRightHamiltonianGraphData T
      (fun n k => R.ambientEmbeddedVector n k)
      (fun n k => R.ambientHamiltonianVector n k) :=
  { mem_rightGeneratorDomain := by
      intro n k
      exact (R.ambientDomainPoint n k).property
    graphDefect_tendsto_zero := by
      intro k
      simpa [ambientEmbeddedVector, embeddedVector, ambientHamiltonianVector,
        finiteVector, ambientDomainPoint] using
        R.rightHamiltonianCompatibility_tendsto_zero k }

/-- The automatically selected positive width at scale `n`. -/
noncomputable def width
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) : NNReal :=
  R.toMovingRightHamiltonianGraphData.width n

/-- Every automatically selected width is strictly positive. -/
theorem width_pos
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) : 0 < R.width n :=
  R.toMovingRightHamiltonianGraphData.width_pos n

/-- The automatically selected widths shrink to zero through positive times. -/
theorem width_tendsto_zero
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap) :
    Tendsto R.width atTop (nhdsWithin 0 (Ioi 0)) := by
  simpa [width] using R.toMovingRightHamiltonianGraphData.width_tendsto_zero

/-- Ambient strong convergence of the selected Wilson vectors. -/
theorem ambientEmbeddedVector_tendsto
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto (fun n => R.ambientEmbeddedVector n k) atTop
      (nhds (((R.spectralVector k : P.VacuumOrthogonalHilbert) :
        P.PhysicalHilbert))) := by
  exact (continuous_subtype_val.tendsto (R.spectralVector k)).comp
    (by simpa [embeddedVector, finiteVector] using R.embeddedVector_tendsto k)

/-- The generic moving-domain diagonal theorem gives the continuum Hamiltonian
difference quotient directly against the embedded finite Hamiltonian action. -/
theorem semigroupDifferenceQuotientCompatibility_tendsto_zero
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        T.rightHamiltonianDifferenceQuotient
            (R.ambientEmbeddedVector n k) (R.width n) -
          R.ambientHamiltonianVector n k)
      atTop (nhds 0) := by
  have h :=
    R.toMovingRightHamiltonianGraphData
      |>.differenceQuotient_sub_target_tendsto_zero k
  simpa [width] using h

/-- Right-generator graph compatibility constructs the shrinking-time-average
strong-limit package without finite-semigroup exponential action or a scaled
common-carrier semigroup defect. -/
noncomputable def toTimeAverageApproximateEigenpairStrongLimitData
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap :=
  { realization := R.realization
    finiteWitness := R.finiteWitness
    SpectralIndex := R.SpectralIndex
    spectralFintype := R.spectralFintype
    finiteIndexEquiv := R.finiteIndexEquiv
    width := R.width
    width_pos := R.width_pos
    width_tendsto_zero := R.width_tendsto_zero
    spectralValue := R.spectralValue
    spectralValue_injective := R.spectralValue_injective
    spectralVector := R.spectralVector
    approximateValue_tendsto := R.approximateValue_tendsto
    embeddedVector_tendsto := R.embeddedVector_tendsto
    semigroupDifferenceQuotientCompatibility_tendsto_zero := by
      intro k
      simpa [ambientEmbeddedVector, embeddedVector, ambientHamiltonianVector,
        finiteVector] using
        R.semigroupDifferenceQuotientCompatibility_tendsto_zero k }

/-- Right-generator graph compatibility constructs the exact continuum resolvent
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  R.toTimeAverageApproximateEigenpairStrongLimitData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Right-generator graph finite Wilson data supply continuum confluent-resolvent
linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (hP : P.IsNormalized) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift =>
            A.toVacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  R.toTimeAverageApproximateEigenpairStrongLimitData
    |>.continuumResolventConfluentCauchy_linearIndependent hP

/-- The same graph transport yields positive-power jet coefficient-map
faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : RightGeneratorGraphData A hInnerSymmetric hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (hFit : A.toVacuumSemigroupGapSlope.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  R.toTimeAverageApproximateEigenpairStrongLimitData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonRightGeneratorGraphStrongLimitData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
