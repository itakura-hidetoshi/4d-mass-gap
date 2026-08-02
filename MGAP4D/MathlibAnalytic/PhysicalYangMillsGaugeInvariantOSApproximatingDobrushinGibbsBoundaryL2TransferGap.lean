import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingDobrushinRateBoundaryL2TransferVacuumIntegralGap

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

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

/-- The real Gibbs `L²` Hilbert space of one finite even-periodic `SU(N)`
Wilson system.

This carrier is deliberately distinct from the shared-boundary Haar `L²`
carrier.  Any route between the two spaces must therefore be supplied by
explicit continuous linear maps. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryGibbsL2
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Type :=
  Lp ℝ 2
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure

/-- A typed bridge from compact Gibbs `L²` dynamics to the actual
shared-boundary Haar `L²` transfer.

At scale `n` and Euclidean time `t`, the boundary transfer is represented as

`boundarySynthesis n t ∘ gibbsEvolution n t ∘ boundaryAnalysis n t`.

The three maps have different mathematical roles:

* `boundaryAnalysis` embeds a shared-boundary moment into the finite Wilson
  Gibbs `L²` carrier;
* `gibbsEvolution` is the Gibbs-side evolution to which a compact heat-bath
  coercive estimate may be applied;
* `boundarySynthesis` returns to the shared-boundary Haar `L²` carrier.

The explicit intertwining field identifies this three-factor composition with
half-time OS translation on the actual boundary moments.  The operator-norm
product field is the exact analytic transport obligation.  In particular, the
structure does not identify the compact heat-bath Hamiltonian with the OS
Hamiltonian and does not infer an `L²` contraction from total variation alone. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
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
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  coefficient_lt_one : coefficient < 1
  dobrushinRayleigh : ∀ n,
    ContinuousCompactOrientedGaugeWilsonDobrushinRayleighCertificate
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength (halfExtent n))
        N hN (beta n) (hbeta n))
  dobrushinRayleigh_coefficient :
    ∀ n, (dobrushinRayleigh n).coefficient = coefficient
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
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n)
  gibbsEvolution :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n)
  boundarySynthesis :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryGibbsL2
          (halfExtent n) N hN (beta n) (hbeta n) →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (boundarySynthesis n t).comp
            ((gibbsEvolution n t).comp (boundaryAnalysis n t))
            (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)
              (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
            (boundaryMoment_memLp n
              (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F)))
  factor_opNorm_mul_le :
    ∀ (n : ℕ) (t : NNReal),
      ‖boundarySynthesis n t‖ *
          (‖gibbsEvolution n t‖ * ‖boundaryAnalysis n t‖) ≤
        Real.sqrt
          (Real.exp
            (-continuousCompactOrientedDobrushinHeatBathGap coefficient *
              (t : ℝ)))

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate

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

/-- The common strict Dobrushin coefficient gives a positive Gibbs-side rate. -/
theorem dobrushinHeatBathGap_pos
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    0 < continuousCompactOrientedDobrushinHeatBathGap Q.coefficient := by
  unfold continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr Q.coefficient_lt_one

/-- The three-factor Gibbs analysis/evolution/synthesis representation controls
the actual shared-boundary transfer norm. -/
theorem boundaryTransfer_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ)
    (t : NNReal) :
    ‖(Q.boundarySynthesis n t).comp
        ((Q.gibbsEvolution n t).comp (Q.boundaryAnalysis n t))‖ ≤
      Real.sqrt
        (Real.exp
          (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficient *
            (t : ℝ))) := by
  calc
    ‖(Q.boundarySynthesis n t).comp
        ((Q.gibbsEvolution n t).comp (Q.boundaryAnalysis n t))‖ ≤
        ‖Q.boundarySynthesis n t‖ *
          ‖(Q.gibbsEvolution n t).comp (Q.boundaryAnalysis n t)‖ :=
      (Q.boundarySynthesis n t).opNorm_comp_le
        ((Q.gibbsEvolution n t).comp (Q.boundaryAnalysis n t))
    _ ≤ ‖Q.boundarySynthesis n t‖ *
          (‖Q.gibbsEvolution n t‖ * ‖Q.boundaryAnalysis n t‖) :=
      mul_le_mul_of_nonneg_left
        ((Q.gibbsEvolution n t).opNorm_comp_le (Q.boundaryAnalysis n t))
        (norm_nonneg (Q.boundarySynthesis n t))
    _ ≤ Real.sqrt
          (Real.exp
            (-continuousCompactOrientedDobrushinHeatBathGap Q.coefficient *
              (t : ℝ))) :=
      Q.factor_opNorm_mul_le n t

/-- Convert the explicit Gibbs-`L²` bridge into the exponential actual
shared-boundary transfer package. -/
noncomputable def toApproximatingExponentialBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingExponentialBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := continuousCompactOrientedDobrushinHeatBathGap Q.coefficient
  mass_pos := Q.dobrushinHeatBathGap_pos
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryTransfer := fun n t =>
    (Q.boundarySynthesis n t).comp
      ((Q.gibbsEvolution n t).comp (Q.boundaryAnalysis n t))
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  boundaryTransfer_opNorm_le := Q.boundaryTransfer_opNorm_le

@[simp] theorem toApproximatingExponentialBoundaryL2TransferGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingExponentialBoundaryL2TransferGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficient :=
  rfl

/-- Package the same bridge in the existing Dobrushin-rate wrapper, preserving
exactly the common coefficient and rate. -/
noncomputable def toApproximatingDobrushinRateBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinRateBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  coefficient := Q.coefficient
  coefficient_nonneg := Q.coefficient_nonneg
  coefficient_lt_one := Q.coefficient_lt_one
  exponentialTransfer :=
    Q.toApproximatingExponentialBoundaryL2TransferGapCertificate
  exponentialTransfer_mass_eq := rfl

/-- The typed Gibbs/shared-boundary bridge therefore feeds the already completed
finite reflected-integral gap route. -/
noncomputable def toApproximatingFiniteIntegralGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingFiniteIntegralGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingDobrushinRateBoundaryL2TransferGapCertificate
    |>.toApproximatingFiniteIntegralGapCertificate

@[simp] theorem toApproximatingFiniteIntegralGapCertificate_mass
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    Q.toApproximatingFiniteIntegralGapCertificate.mass =
      continuousCompactOrientedDobrushinHeatBathGap Q.coefficient :=
  rfl

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingDobrushinGibbsBoundaryL2TransferGapCertificate

end MathlibAnalytic
end MGAP4D

end
