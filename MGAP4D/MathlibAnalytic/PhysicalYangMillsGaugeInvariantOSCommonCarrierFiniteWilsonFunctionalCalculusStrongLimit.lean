import MGAP4D.MathlibAnalytic.FiniteWilsonFiniteDimensionalHamiltonianExponentialOperator
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonSemigroupDefectStrongLimit
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

/-- Selected finite Wilson spectra whose actual finite OS semigroup agrees, on
the whole realized Hamiltonian sector, with the finite-dimensional exponential
functional calculus.

This structural intertwining theorem generates the selected `exp (-E t)`
eigenaction required by the semigroup-defect strong-limit package. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonFunctionalCalculusStrongLimitData
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
  width : ℕ → NNReal
  width_pos : ∀ n, 0 < width n
  width_tendsto_zero :
    Tendsto width atTop (nhdsWithin 0 (Ioi 0))
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
  finiteSemigroupFunctionalCalculus :
    ∀ n t phi,
      C.finiteOperator n t (realization.finiteRealization n phi) =
        realization.finiteRealization n
          (F.hamiltonianExponentialOperator n t phi)
  scaledCommonCarrierSemigroupDefect_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          let phi :=
            (finiteWitness n).spectralVector (finiteIndexEquiv n k)
          let ambient :=
            ((realization.excitationEmbed n phi : P.VacuumOrthogonalHilbert) :
              P.PhysicalHilbert)
          (((width n : NNReal) : ℝ))⁻¹ •
            (A.embed n
                (C.finiteOperator n (width n)
                  (realization.finiteRealization n phi)) -
              T.toPhysicalSemigroup.operator (width n) ambient))
        atTop (nhds 0)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonFunctionalCalculusStrongLimitData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonFunctionalCalculusStrongLimitData

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

abbrev FunctionalCalculusData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonFunctionalCalculusStrongLimitData
    A hInnerSymmetric hSelf F nodes orderCap

/-- The selected finite Wilson energy. -/
def approximateValue
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The selected finite Wilson Hamiltonian eigenvector. -/
def finiteVector
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- Full realized-sector functional-calculus intertwining generates the selected
finite-semigroup exponential eigenaction. -/
theorem finiteSemigroup_eigenaction
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    C.finiteOperator n (R.width n)
        (R.realization.finiteRealization n (R.finiteVector n k)) =
      Real.exp
          (-R.approximateValue n k * (((R.width n : NNReal) : ℝ))) •
        R.realization.finiteRealization n (R.finiteVector n k) := by
  calc
    C.finiteOperator n (R.width n)
        (R.realization.finiteRealization n (R.finiteVector n k)) =
        R.realization.finiteRealization n
          (F.hamiltonianExponentialOperator n (R.width n)
            (R.finiteVector n k)) :=
      R.finiteSemigroupFunctionalCalculus n (R.width n) (R.finiteVector n k)
    _ = R.realization.finiteRealization n
          (Real.exp
              (-R.approximateValue n k * (((R.width n : NNReal) : ℝ))) •
            R.finiteVector n k) := by
      rw [finite_wilson_hamiltonianExponentialOperator_apply_spectralVector
        F n
        (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift => sigma.1)
        nodes orderCap (R.finiteWitness n) (R.width n) (R.finiteIndexEquiv n k)]
    _ = Real.exp
          (-R.approximateValue n k * (((R.width n : NNReal) : ℝ))) •
        R.realization.finiteRealization n (R.finiteVector n k) := by
      rw [map_smul]

/-- Forget the full functional-calculus presentation only after deriving the
selected exponential semigroup action. -/
noncomputable def toExponentialSemigroupDefectStrongLimitData
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExponentialSemigroupDefectStrongLimitData
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
    finiteSemigroup_eigenaction := by
      intro n k
      simpa [finiteVector, approximateValue] using
        R.finiteSemigroup_eigenaction n k
    scaledCommonCarrierSemigroupDefect_tendsto_zero :=
      R.scaledCommonCarrierSemigroupDefect_tendsto_zero }

/-- Functional-calculus intertwining constructs the shrinking-time-average
strong-limit package. -/
noncomputable def toTimeAverageApproximateEigenpairStrongLimitData
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap :=
  R.toExponentialSemigroupDefectStrongLimitData
    |>.toTimeAverageApproximateEigenpairStrongLimitData

/-- Functional-calculus intertwining constructs the exact continuum
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  R.toExponentialSemigroupDefectStrongLimitData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Functional-calculus finite Wilson data supply continuum confluent-resolvent
linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap)
    (hP : P.IsNormalized) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift =>
            A.toVacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  R.toExponentialSemigroupDefectStrongLimitData
    |>.continuumResolventConfluentCauchy_linearIndependent hP

/-- The same functional-calculus transport yields positive-power jet
coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : FunctionalCalculusData A hInnerSymmetric hSelf F nodes orderCap)
    (hP : P.IsNormalized)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (hFit : A.toVacuumSemigroupGapSlope.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  R.toExponentialSemigroupDefectStrongLimitData
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonFunctionalCalculusStrongLimitData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
