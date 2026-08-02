import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingUniformDobrushinGibbsBoundaryL2TransferVacuumIntegralGap

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProduct InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A finite Wilson OS bridge using the canonical boundary Haar-to-Gibbs
analysis isometry constructed from the actual measure geometry.

There is no arbitrary boundary-analysis map in this certificate.  At scale
`n` the map is definitionally the composition

`boundary Haar L² → configuration Haar L² → Wilson Gibbs L²`,

where the first arrow is pullback along the genuine reflection-fixed boundary
projection and the second is multiplication by the inverse square root of the
normalized Wilson Gibbs density.  The centered heat-bath evolution itself
applies the normalized-vacuum projection, so no separate centered-image
assumption is required.

The exact relation to OS Euclidean-time translation remains the explicit
boundary-moment intertwining field.  No identification of the heat-bath and OS
Hamiltonians is made. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) where
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficientBound_lt_one : coefficientBound < 1
  dobrushinMatrix : ∀ n,
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n))
  coefficient_le_bound :
    ∀ n, (dobrushinMatrix n).coefficient ≤ coefficientBound
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  gram_integrable :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
      (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
        (halfExtent n) N),
      Integrable
        (periodicHypercubicEvenBoundaryObservableGramFeature
          (halfExtent n) N hN (beta n) (hbeta n)
          (fun x =>
            physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
              S D halfExtent N hN beta hbeta B hInvariant n F x)
          b)
        (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta B hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      let An :=
        periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
          (halfExtent n) N hN (beta n) (hbeta n)
      ∀ F : Pn.Carrier,
        (An.toContinuousLinearMap†)
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength (halfExtent n))
              N hN (beta n) (hbeta n)).centeredHeatBathEvolutionL2 t
              (An
                (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
                  S D halfExtent N hN beta hbeta B hInvariant n
                  (Pn.vacuumCenteredCarrier F)
                  (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))))) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
            (boundaryMoment_memLp n
              (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- The common strict coefficient bound gives a positive heat-bath gap. -/
theorem uniformGap_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    0 < continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound := by
  unfold continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr Q.coefficientBound_lt_one

/-- Native Dobrushin Poincaré coercivity generates the centered heat-bath
operator norm at every scale. -/
theorem centeredHeatBathEvolution_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (t : NNReal) :
    ‖(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n)).centeredHeatBathEvolutionL2 t‖ ≤
      Real.sqrt
        (Real.exp
          (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
            (t : ℝ))) := by
  let W := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength (halfExtent n))
    N hN (beta n) (hbeta n)
  exact
    continuous_compact_oriented_centeredHeatBathEvolutionL2_opNorm_le
      W
      (continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound)
      (continuous_compact_oriented_dobrushinCoefficientBoundHeatBathPoincareL2
        W (Q.dobrushinMatrix n)
        Q.coefficientBound Q.coefficientBound_nonneg Q.coefficientBound_lt_one
        (Q.coefficient_le_bound n))
      t

/-- Convert the fully constructed boundary analysis and generated heat-bath
norm estimate into the established uniform shared-boundary transfer package. -/
noncomputable def toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  coefficientBound := Q.coefficientBound
  coefficientBound_nonneg := Q.coefficientBound_nonneg
  coefficientBound_lt_one := Q.coefficientBound_lt_one
  dobrushinMatrix := Q.dobrushinMatrix
  coefficient_le_bound := Q.coefficient_le_bound
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryAnalysis := fun n _t =>
    (periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
      (halfExtent n) N hN (beta n) (hbeta n)).toContinuousLinearMap
  gibbsEvolution := fun n t =>
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).centeredHeatBathEvolutionL2 t
  boundarySynthesis := fun n _t =>
    realHilbertAdjointSynthesis
      (periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
        (halfExtent n) N hN (beta n) (hbeta n))
  boundaryAnalysis_opNorm_le_one := by
    intro n t
    exact realHilbertLinearIsometry_opNorm_le_one
      (periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
        (halfExtent n) N hN (beta n) (hbeta n))
  gibbsEvolution_opNorm_le := by
    intro n t
    exact Q.centeredHeatBathEvolution_opNorm_le n t
  boundarySynthesis_opNorm_le_one := by
    intro n t
    exact realHilbertAdjointSynthesis_opNorm_le_one
      (periodicHypercubicEvenSpecialUnitaryBoundaryHaarGibbsL2Analysis
        (halfExtent n) N hN (beta n) (hbeta n))
  boundaryMoment_intertwining := by
    intro n t
    dsimp
    intro F
    exact Q.boundaryMoment_intertwining n t F

/-- Actual finite periodic Wilson reflected-integral decay follows with the
same common Dobrushin mass. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- Completed nonnegative vacuum decay follows automatically. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    |>.toApproximatingNonnegativeVacuumGapCertificate

@[simp] theorem toApproximatingFiniteIntegralGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate

/-- Common-carrier continuum endpoint generated by the canonical boundary
Haar-to-Gibbs analysis package. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryHaarGibbsHeatBathCommonCarrierGapTransfer
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryHaarGibbsHeatBathCommonCarrierGapTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
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
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCanonicalBoundaryHaarGibbsHeatBathTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- Continuum right-Hamiltonian coercivity inherits the exact common
Dobrushin rate. -/
theorem rightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryHaarGibbsHeatBathCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) :=
  PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer.rightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    A psi hpsi

/-- The same lower bound survives graph closure. -/
theorem closedRightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryHaarGibbsHeatBathCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) :=
  PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer.closedRightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    A hP psi hpsi

/-- The graph-closed continuum Hamiltonian has exactly the normalized vacuum
line as zero-energy space. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryHaarGibbsHeatBathCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum :=
  PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryHaarGibbsHeatBathCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
