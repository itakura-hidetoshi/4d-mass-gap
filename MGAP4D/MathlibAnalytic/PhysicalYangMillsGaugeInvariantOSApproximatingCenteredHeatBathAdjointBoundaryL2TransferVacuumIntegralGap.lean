import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonCenteredHeatBathEnergyDecay
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

/-- A centered, adjoint-factorized finite Wilson bridge.

The full Gibbs heat-bath evolution fixes the normalized Gibbs vacuum, so it
cannot contract below one on the full Hilbert space.  The actual dynamic map
used here is therefore

`exp (-(t / 2) H_HB) ∘ P_vacuum⊥`,

where the vacuum-centering projection is the explicit rank-one formula
`f ↦ f - ⟪Ω,f⟫ Ω`.  Boundary analysis is one linear isometry into the actual
finite Wilson Gibbs `L²` carrier, and synthesis is generated canonically as
its Hilbert adjoint.

The heat-bath and OS Hamiltonians remain distinct.  Their exact relation is
kept in the boundary-moment intertwining field. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate

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

/-- The common strict coefficient bound gives a positive rate. -/
theorem uniformGap_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    0 < continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound := by
  unfold continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr Q.coefficientBound_lt_one

/-- At every scale, the actual finite Wilson heat-bath Hamiltonian is coercive
on the Gibbs-vacuum orthogonal sector with the common coefficient-bound gap. -/
theorem heatBathHamiltonian_coercive
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryGibbsL2
      (halfExtent n) N hN (beta n) (hbeta n))
    (hf : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n)).gibbsVacuumL2 f = 0) :
    continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
        ‖f‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength (halfExtent n))
          N hN (beta n) (hbeta n)).heatBathHamiltonianL2 f) f := by
  let W := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength (halfExtent n))
    N hN (beta n) (hbeta n)
  exact
    continuous_compact_oriented_centeredHeatBathHamiltonianL2_coercive
      W
      (continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound)
      (continuous_compact_oriented_dobrushinCoefficientBoundHeatBathPoincareL2
        W (Q.dobrushinMatrix n)
        Q.coefficientBound Q.coefficientBound_nonneg Q.coefficientBound_lt_one
        (Q.coefficient_le_bound n))
      f hf

/-- The actual finite Wilson centered heat-bath exponential contraction is
now generated at every scale from the common Dobrushin Poincaré gap. -/
theorem centeredHeatBathEvolution_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
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

/-- Convert the isometry/adjoint/explicit-centered-exponential package into
the previous uniform Gibbs/shared-boundary transfer certificate. -/
noncomputable def toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
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
    (Q.boundaryAnalysis n).toContinuousLinearMap
  gibbsEvolution := fun n t =>
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength (halfExtent n))
      N hN (beta n) (hbeta n)).centeredHeatBathEvolutionL2 t
  boundarySynthesis := fun n _t =>
    realHilbertAdjointSynthesis (Q.boundaryAnalysis n)
  boundaryAnalysis_opNorm_le_one := by
    intro n t
    exact realHilbertLinearIsometry_opNorm_le_one (Q.boundaryAnalysis n)
  gibbsEvolution_opNorm_le := by
    intro n t
    exact Q.centeredHeatBathEvolution_opNorm_le n t
  boundarySynthesis_opNorm_le_one := by
    intro n t
    exact realHilbertAdjointSynthesis_opNorm_le_one (Q.boundaryAnalysis n)
  boundaryMoment_intertwining := by
    intro n t
    dsimp
    intro F
    exact Q.boundaryMoment_intertwining n t F

/-- The centered package generates the exponential actual shared-boundary
transfer contraction. -/
noncomputable def toApproximatingExponentialBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    |>.toApproximatingExponentialBoundaryL2TransferGapCertificate

/-- It also generates the actual finite periodic Wilson reflected-integral gap
with the same common mass. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

/-- Completed nonnegative vacuum decay follows automatically. -/
noncomputable def toApproximatingNonnegativeVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate
    |>.toApproximatingNonnegativeVacuumGapCertificate

@[simp] theorem toApproximatingFiniteIntegralGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound :=
  rfl

@[simp] theorem nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (t : NNReal) :
    (PhysicalYangMillsEvenPeriodicWilsonOSApproximatingNonnegativeVacuumGapCertificate.toApproximatingFiniteIntegralGapCertificate
      Q.toApproximatingNonnegativeVacuumGapCertificate).quadraticDecayFactor t =
      Real.exp
        (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficientBound *
          (t : ℝ)) := by
  exact
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingUniformDobrushinGibbsBoundaryL2TransferGapCertificate.nonnegativeVacuum_finiteIntegral_roundTrip_quadraticDecayFactor
      Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate t

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate

/-- Common-carrier continuum endpoint generated by the centered heat-bath
adjoint boundary package. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer
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
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :=
  PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer
    S D halfExtent N hN beta hbeta B hInvariant P T C
      Q.toUniformDobrushinGibbsBoundaryL2TransferGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer

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
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingCenteredHeatBathAdjointBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- Continuum right-Hamiltonian coercivity inherits the exact common
Dobrushin rate. -/
theorem rightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer
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
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer
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
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum :=
  PhysicalYangMillsEvenPeriodicWilsonOSUniformDobrushinGibbsBoundaryL2TransferCommonCarrierGapTransfer.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    A hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSCenteredHeatBathAdjointBoundaryL2TransferCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end