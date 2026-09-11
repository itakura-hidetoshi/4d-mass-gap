import MGAP4D.MathlibAnalytic.FiniteFamilyPositiveDiagonalSelection
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonGeneratorExponentialDefect
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

/-- Common spectral data equipped with actual finite Wilson OS generator
intertwining.  The shrinking widths are not inputs: they are selected
canonically below from the finite family of local generator defects. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorSpectralStrongLimitData
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
  generator :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorIntertwiningData
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
          generator.realization.excitationEmbed n
            ((finiteWitness n).spectralVector (finiteIndexEquiv n k)))
        atTop (nhds (spectralVector k))

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorSpectralStrongLimitData.spectralFintype

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorSpectralStrongLimitData

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

abbrev GeneratorSpectralData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W)
    [DecidableEq A.toVacuumSemigroupGapSlope.BelowHalfMassShift]
    (nodes : Finset A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (orderCap : ℕ) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorSpectralStrongLimitData
    A hInnerSymmetric hSelf F nodes orderCap

/-- The selected finite Wilson energy. -/
def approximateValue
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : ℝ :=
  (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k)

/-- The selected finite Wilson Hamiltonian eigenvector. -/
def finiteVector
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : F.StateSpace :=
  (R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)

/-- The scaled local defect between the scalar exponential model and the actual
finite Wilson OS semigroup. -/
noncomputable def finiteScaledExponentialDefect
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (t : NNReal) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n :=
  (((t : NNReal) : ℝ))⁻¹ •
    (Real.exp (-R.approximateValue n k * (((t : NNReal) : ℝ))) •
        R.generator.realization.finiteRealization n (R.finiteVector n k) -
      C.finiteOperator n t
        (R.generator.realization.finiteRealization n (R.finiteVector n k)))

/-- Scalar norm of the finite scaled exponential-model defect. -/
noncomputable def finiteScaledExponentialDefectNorm
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) (t : NNReal) : ℝ :=
  ‖R.finiteScaledExponentialDefect n k t‖

/-- Generator intertwining makes every finite scaled defect norm tend to zero at
positive time zero. -/
theorem finiteScaledExponentialDefectNorm_tendsto_zero
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    Tendsto (R.finiteScaledExponentialDefectNorm n k)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h :=
    R.generator.finiteExponentialModelDefect_tendsto_spectralVector
      n
      (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift => sigma.1)
      nodes orderCap (R.finiteWitness n) (R.finiteIndexEquiv n k)
  have hnorm := (continuous_norm.tendsto 0).comp h
  change Tendsto
    (fun t : NNReal => ‖R.finiteScaledExponentialDefect n k t‖)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)
  simpa [Function.comp_def, finiteScaledExponentialDefect, finiteVector,
    approximateValue] using hnorm

/-- Canonical simultaneous shrinking-time selection for all selected spectral
indices. -/
noncomputable def diagonalSelection
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap) :
    FiniteFamilyPositiveDiagonalSelectionData
      (fun n k t => R.finiteScaledExponentialDefectNorm n k t) :=
  FiniteFamilyPositiveDiagonalSelectionData.of_tendsto
    R.finiteScaledExponentialDefectNorm_tendsto_zero

/-- The automatically selected positive width at scale `n`. -/
noncomputable def width
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) : NNReal :=
  R.diagonalSelection.width n

/-- Every automatically selected width is positive. -/
theorem width_pos
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) : 0 < R.width n :=
  R.diagonalSelection.width_pos n

/-- The automatically selected widths shrink to zero through positive times. -/
theorem width_tendsto_zero
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap) :
    Tendsto R.width atTop (nhdsWithin 0 (Ioi 0)) := by
  simpa [width] using R.diagonalSelection.width_tendsto_zero

/-- Every selected finite scaled exponential defect tends to zero along the one
common diagonal width sequence. -/
theorem finiteScaledExponentialDefectNorm_diagonal_tendsto_zero
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n => R.finiteScaledExponentialDefectNorm n k (R.width n))
      atTop (nhds 0) := by
  simpa [width] using R.diagonalSelection.defect_tendsto_zero k

/-- The selected vector embedded in the continuum excitation carrier. -/
noncomputable def embeddedVector
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.VacuumOrthogonalHilbert :=
  R.generator.realization.excitationEmbed n (R.finiteVector n k)

/-- The selected embedded vector in the ambient continuum Hilbert space. -/
noncomputable def ambientEmbeddedVector
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) : P.PhysicalHilbert :=
  ((R.embeddedVector n k : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)

/-- Ambient strong convergence of the selected vectors. -/
theorem ambientEmbeddedVector_tendsto
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto (fun n => R.ambientEmbeddedVector n k) atTop
      (nhds (((R.spectralVector k : P.VacuumOrthogonalHilbert) :
        P.PhysicalHilbert))) := by
  exact (continuous_subtype_val.tendsto (R.spectralVector k)).comp
    (by simpa [embeddedVector, finiteVector] using R.embeddedVector_tendsto k)

/-- Isometric common-carrier embedding preserves the selected finite defect
convergence. -/
theorem embeddedFiniteScaledExponentialDefect_tendsto_zero
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n => A.embed n
        (R.finiteScaledExponentialDefect n k (R.width n)))
      atTop (nhds 0) := by
  have hnorm := R.finiteScaledExponentialDefectNorm_diagonal_tendsto_zero k
  rw [Metric.tendsto_nhds] at hnorm ⊢
  intro epsilon hepsilon
  have hevent := hnorm epsilon hepsilon
  filter_upwards [hevent] with n hn
  simpa [finiteScaledExponentialDefectNorm, dist_zero_right, A.embed_norm,
    Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hn

/-- Common-carrier input retained after the finite generator defects have chosen
the shrinking widths automatically. -/
structure GeneratorDiagonalCommonCarrierDefectData
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap) where
  scaledCommonCarrierSemigroupDefect_tendsto_zero :
    ∀ k,
      Tendsto
        (fun n =>
          (((R.width n : NNReal) : ℝ))⁻¹ •
            (A.embed n
                (C.finiteOperator n (R.width n)
                  (R.generator.realization.finiteRealization n
                    (R.finiteVector n k))) -
              T.toPhysicalSemigroup.operator (R.width n)
                (R.ambientEmbeddedVector n k)))
        atTop (nhds 0)

/-- The selected finite energies are strictly positive. -/
theorem approximateValue_pos
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    0 < R.approximateValue n k :=
  lt_of_lt_of_le exactGapValueReal_pos
    ((R.finiteWitness n).spectralValue_ge_exactGap (R.finiteIndexEquiv n k))

/-- The automatically selected finite generator defect and the retained
common-carrier defect add to the continuum scalar exponential-model defect. -/
theorem exponentialModelDefect_tendsto_zero
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (H : GeneratorDiagonalCommonCarrierDefectData R)
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
  have hsum :=
    (R.embeddedFiniteScaledExponentialDefect_tendsto_zero k).add
      (H.scaledCommonCarrierSemigroupDefect_tendsto_zero k)
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
        A.embed n (R.finiteScaledExponentialDefect n k (R.width n)) +
          (((R.width n : NNReal) : ℝ))⁻¹ •
            (A.embed n
                (C.finiteOperator n (R.width n)
                  (R.generator.realization.finiteRealization n
                    (R.finiteVector n k))) -
              T.toPhysicalSemigroup.operator (R.width n)
                (R.ambientEmbeddedVector n k))) := by
    funext n
    dsimp [finiteScaledExponentialDefect, ambientEmbeddedVector,
      embeddedVector]
    rw [map_smul, map_sub, map_smul]
    module
  rw [hfunction]
  simpa only [zero_add] using hsum

/-- The finite Hamiltonian eigen-equation transported to the ambient carrier. -/
theorem ambientEmbed_hamiltonian_finiteVector
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (n : ℕ) (k : R.SpectralIndex) :
    (((R.generator.realization.excitationEmbed n
          (F.hamiltonian n (R.finiteVector n k)) :
        P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)) =
      R.approximateValue n k • R.ambientEmbeddedVector n k := by
  change
    A.embed n
        (R.generator.realization.finiteRealization n
          (F.hamiltonian n
            ((R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)))) =
      (R.finiteWitness n).spectralValue (R.finiteIndexEquiv n k) •
        A.embed n
          (R.generator.realization.finiteRealization n
            ((R.finiteWitness n).spectralVector (R.finiteIndexEquiv n k)))
  rw [(R.finiteWitness n).hamiltonian_apply_spectralVector, map_smul, map_smul]

/-- Generator-selected finite defects plus the common-carrier defect produce the
full continuum Hamiltonian difference-quotient compatibility. -/
theorem semigroupDifferenceQuotientCompatibility_tendsto_zero
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (H : GeneratorDiagonalCommonCarrierDefectData R)
    (k : R.SpectralIndex) :
    Tendsto
      (fun n =>
        T.rightHamiltonianDifferenceQuotient
            (R.ambientEmbeddedVector n k) (R.width n) -
          (((R.generator.realization.excitationEmbed n
                (F.hamiltonian n (R.finiteVector n k)) :
              P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)))
      atTop (nhds 0) := by
  have hgeneric :=
    T.rightHamiltonianDifferenceQuotient_sub_energy_smul_tendsto_zero_of_exponentialModel
      R.width_pos R.width_tendsto_zero
      (fun n => R.approximateValue_pos n k)
      (by simpa [approximateValue] using R.approximateValue_tendsto k)
      (R.ambientEmbeddedVector_tendsto k)
      (R.exponentialModelDefect_tendsto_zero H k)
  have hfunction :
      (fun n =>
        T.rightHamiltonianDifferenceQuotient
            (R.ambientEmbeddedVector n k) (R.width n) -
          (((R.generator.realization.excitationEmbed n
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

/-- The generator-level package with automatically selected widths constructs
the shrinking-time-average strong-limit data without exact finite-semigroup
eigenaction. -/
noncomputable def toTimeAverageApproximateEigenpairStrongLimitData
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (H : GeneratorDiagonalCommonCarrierDefectData R) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonTimeAverageApproximateEigenpairStrongLimitData
      A hInnerSymmetric hSelf F nodes orderCap :=
  { realization := R.generator.realization
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
        R.semigroupDifferenceQuotientCompatibility_tendsto_zero H k }

/-- The generator-diagonal package constructs the exact continuum resolvent
approximate-eigenpair strong-limit package. -/
noncomputable def toContinuumResolventApproximateEigenpairStrongLimitData
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (H : GeneratorDiagonalCommonCarrierDefectData R) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap :=
  (R.toTimeAverageApproximateEigenpairStrongLimitData H)
    |>.toContinuumResolventApproximateEigenpairStrongLimitData

/-- Generator-level finite Wilson data with diagonal selection supply continuum
confluent-resolvent linear independence. -/
theorem continuumResolventConfluentCauchy_linearIndependent
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (H : GeneratorDiagonalCommonCarrierDefectData R)
    (hP : P.IsNormalized) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : A.toVacuumSemigroupGapSlope.BelowHalfMassShift =>
            A.toVacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  (R.toTimeAverageApproximateEigenpairStrongLimitData H)
    |>.continuumResolventConfluentCauchy_linearIndependent hP

/-- The same generator-diagonal transport yields positive-power jet coefficient
map faithfulness. -/
theorem continuumResolventPositivePowerJetCoefficientMapsIndependent
    (R : GeneratorSpectralData A hInnerSymmetric hSelf F nodes orderCap)
    (H : GeneratorDiagonalCommonCarrierDefectData R)
    (hP : P.IsNormalized)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      A.toVacuumSemigroupGapSlope.BelowHalfMassShift)
    (hFit : A.toVacuumSemigroupGapSlope.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    A.toVacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  (R.toTimeAverageApproximateEigenpairStrongLimitData H)
    |>.continuumResolventPositivePowerJetCoefficientMapsIndependent
      hP left right hFit

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorSpectralStrongLimitData

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
