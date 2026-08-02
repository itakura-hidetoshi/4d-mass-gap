import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredHeatBathEnergyDecay
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferVacuumIntegralGap

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

/-- A centered finite Wilson boundary bridge whose heat-bath exponential
contraction is generated from the native Dobrushin coefficient-bound
Poincaré theorem.

Unlike the preceding adjoint-factorized certificate, this structure contains
no independent operator-norm decay field.  Its remaining model-specific data
are the boundary analysis isometry, its centered image, and the exact OS
boundary-moment intertwining. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
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
  boundaryAnalysis :
    ∀ n,
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →ₗᵢ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n)
  boundaryAnalysis_centered :
    ∀ n v,
      inner ℝ
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).gibbsVacuumL2
        (boundaryAnalysis n v) = 0
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (((boundaryAnalysis n).toContinuousLinearMap)†)
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength (halfExtent n))
              N hN (beta n) (hbeta n)).centeredHeatBathEvolutionL2 t
              (boundaryAnalysis n
                (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
                  S D halfExtent N hN beta hbeta B hInvariant n
                  (Pn.vacuumCenteredCarrier F)
                  (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))))) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
            (boundaryMoment_memLp n
              (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate

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

/-- The native finite Wilson Dobrushin Poincaré theorem generates the exact
centered heat-bath operator-norm decay at every scale. -/
theorem centeredHeatBathEvolution_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
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

/-- Convert to the preceding adjoint-factorized certificate, filling its only
remaining analytic norm field from coercivity. -/
noncomputable def toCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  coefficientBound := Q.coefficientBound
  coefficientBound_nonneg := Q.coefficientBound_nonneg
  coefficientBound_lt_one := Q.coefficientBound_lt_one
  dobrushinMatrix := Q.dobrushinMatrix
  coefficient_le_bound := Q.coefficient_le_bound
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryAnalysis := Q.boundaryAnalysis
  boundaryAnalysis_centered := Q.boundaryAnalysis_centered
  centeredHeatBathEvolution_opNorm_le := by
    intro n t
    exact Q.centeredHeatBathEvolution_opNorm_le n t
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining

/-- The coercive endpoint generates the uniform Gibbs/shared-boundary transfer
certificate without an independent dynamic norm assumption. -/
noncomputable def toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
    |>.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate

/-- Actual finite periodic Wilson reflected-integral decay follows with the
same common Dobrushin mass. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- Completed nonnegative vacuum decay also follows automatically. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
    |>.toApproximatingNonnegativeVacuumGapCertificate

@[simp] theorem toApproximatingFiniteIntegralGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate

/-- Common-carrier continuum endpoint generated after the centered heat-bath
operator norm has been discharged from finite Wilson coercivity. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSCoerciveCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer
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
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCoerciveCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toCenteredHeatBathAdjointBoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end
