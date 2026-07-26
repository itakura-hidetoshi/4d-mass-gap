import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSMovingExponentialDifferenceQuotient
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

/-- Selected finite Wilson eigenvectors with exact finite-semigroup exponential
eigenaction and an `o(h)` common-carrier semigroup intertwining defect. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExponentialSemigroupDefectStrongLimitData
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
  finiteSemigroup_eigenaction :
    ∀ n k,
      let phi :=
        (finiteWitness n).spectralVector (finiteIndexEquiv n k)
      let energy :=
        (finiteWitness n).spectralValue (finiteIndexEquiv n k)
      C.finiteOperator n (width n)
          (realization.finiteRealization n phi) =
        Real.exp (-energy * (((width n : NNReal) : ℝ))) •
          realization.finiteRealization n phi
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
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExponentialSemigroupDefectStrongLimitData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExponentialSemigroupDefectStrongLimitData

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

abbrev DefectData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExponentialSemigroupDefectStrongLimitData
    A hInnerSymmetric hSelf F nodes orderCap

/-- The selected finite Wilson energy. -/
def approximateValue
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The selected finite Wilson eigenvector. -/
def finiteVector
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The selected vector embedded in the continuum excitation carrier. -/
noncomputable def embeddedVector
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  R.realization.excitationEmbed n (R.finiteVector n k)

/-- The selected embedded vector in the ambient continuum Hilbert space. -/
noncomputable def ambientEmbeddedVector
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  ((R.embeddedVector n k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)

/-- Selected finite Wilson energies are strictly positive. -/
theorem approximateValue_pos
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    0 < R.approximateValue n k :=
  lt_of_lt_of_le exactGapValueReal_pos
    ((R.finiteWitness n).spectralValue_ge_exactGap (R.finiteIndexEquiv n k))

/-- The named embedded-vector sequence has the supplied strong limit. -/
theorem embeddedVector_tendsto_named
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto (fun n => R.embeddedVector n k) atTop
      (nhds (R.spectralVector k)) := by
  simpa [embeddedVector, finiteVector] using R.embeddedVector_tendsto k

/-- Ambient strong convergence of the selected vectors. -/
theorem ambientEmbeddedVector_tendsto
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto (fun n => R.ambientEmbeddedVector n k) atTop
      (nhds (((R.spectralVector k : P.VacuumOrthogonalHilbert) :
        P.PhysicalHilbert))) := by
  exact (continuous_subtype_val.tendsto (R.spectralVector k)).comp
    (R.embeddedVector_tendsto_named k)

/-- The finite exponential eigenaction survives common-carrier embedding. -/
theorem embeddedFiniteSemigroup_eigenaction
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    A.embed n
        (C.finiteOperator n (R.width n)
          (R.realization.finiteRealization n (R.finiteVector n k))) =
      Real.exp
          (-R.approximateValue n k *
            (((R.width n : NNReal) : ℝ))) •
        R.ambientEmbeddedVector n k := by
  have h := congrArg (fun psi => A.embed n psi)
    (R.finiteSemigroup_eigenaction n k)
  simpa [finiteVector, approximateValue, ambientEmbeddedVector, embeddedVector]
    using h

/-- The supplied scaled common-carrier defect is the generic exponential-model
defect. -/
theorem exponentialModelDefect_tendsto_zero
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        (((R.width n : NNReal) : ℝ))⁻¹ •
          (Real.exp
                (-R.approximateValue n k *
                  (((R.width n : NNReal) : ℝ))) •
              R.ambientEmbeddedVector n k -
            T.toPhysicalSemigroup.operator (R.width n)
              (R.ambientEmbeddedVector n k)))
      atTop (nhds 0) := by
  have h := R.scaledCommonCarrierSemigroupDefect_tendsto_zero k
  have hfunction :
      (fun n =>
        (((R.width n : NNReal) : ℝ))⁻¹ •
          (Real.exp
                (-R.approximateValue n k *
                  (((R.width n : NNReal) : ℝ))) •
              R.ambientEmbeddedVector n k -
            T.toPhysicalSemigroup.operator (R.width n)
              (R.ambientEmbeddedVector n k))) =
      (fun n =>
        let phi :=
          (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)
        let ambient :=
          ((R.realization.excitationEmbed n phi : P.VacuumOrthogonalHilbert) :
            P.PhysicalHilbert)
        (((R.width n : NNReal) : ℝ))⁻¹ •
          (A.embed n
              (C.finiteOperator n (R.width n)
                (R.realization.finiteRealization n phi)) -
            T.toPhysicalSemigroup.operator (R.width n) ambient)) := by
    funext n
    dsimp [approximateValue, ambientEmbeddedVector, embeddedVector, finiteVector]
    rw [R.embeddedFiniteSemigroup_eigenaction n k]
  rw [hfunction]
  exact h

/-- The finite Hamiltonian eigen-equation transported to the ambient carrier. -/
theorem ambientEmbed_hamiltonian_finiteVector
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (((R.realization.excitationEmbed n
          (F.hamiltonian n (R.finiteVector n k)) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
      R.approximateValue n k • R.ambientEmbeddedVector n k := by
  change
    A.embed n
        (R.realization.finiteRealization n
          (F.hamiltonian n
            ((R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)))) =
      (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k) •
        A.embed n
          (R.realization.finiteRealization n
            ((R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)))
  rw [(R.finiteWitness n).hamiltonian_apply_spectralVector, map_smul, map_smul]

/-- Exponential finite-semigroup eigenaction plus an `o(h)` common-carrier defect
produce full Hamiltonian difference-quotient compatibility. -/
theorem semigroupDifferenceQuotientCompatibility_tendsto_zero
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        T.rightHamiltonianDifferenceQuotient
            (R.ambientEmbeddedVector n k) (R.width n) -
          (((R.realization.excitationEmbed n
                (F.hamiltonian n (R.finiteVector n k)) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
      atTop (nhds 0) := by
  have hgeneric :=
    T.rightHamiltonianDifferenceQuotient_sub_energy_smul_tendsto_zero_of_exponentialModel
      R.width_pos R.width_tendsto_zero
      (fun n => R.approximateValue_pos n k)
      (by simpa [approximateValue] using R.approximateValue_tendsto k)
      (R.ambientEmbeddedVector_tendsto k)
      (R.exponentialModelDefect_tendsto_zero k)
  have hfunction :
      (fun n =>
        T.rightHamiltonianDifferenceQuotient
            (R.ambientEmbeddedVector n k) (R.width n) -
          (((R.realization.excitationEmbed n
                (F.hamiltonian n (R.finiteVector n k)) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert))) =
      (fun n =>
        T.rightHamiltonianDifferenceQuotient
            (R.ambientEmbeddedVector n k) (R.width n) -
          R.approximateValue n k • R.ambientEmbeddedVector n k) := by
    funext n
    rw [R.ambientEmbed_hamiltonian_finiteVector n k]
  rw [hfunction]
  exact hgeneric

/-- Forget the exponential semigroup presentation after deriving the previous
shrinking-time package. -/
noncomputable def toTimeAverageApproximateEigenpairStrongLimitData
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap) :
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
      simpa [ambientEmbeddedVector, embeddedVector, finiteVector] using
        R.semigroupDifferenceQuotientCompatibility_tendsto_zero k }

/-- Quantitative semigroup defects construct the continuum approximate-eigenpair
strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  R.toTimeAverageApproximateEigenpairStrongLimitData
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Quantitative semigroup defects supply continuum confluent-resolvent linear
independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
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

/-- The same transport yields positive-power jet coefficient-map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : DefectData A hInnerSymmetric hSelf F nodes orderCap)
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

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExponentialSemigroupDefectStrongLimitData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
