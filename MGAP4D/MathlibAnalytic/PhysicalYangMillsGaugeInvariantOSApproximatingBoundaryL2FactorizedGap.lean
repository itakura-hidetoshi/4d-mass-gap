import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2TransferGap

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A shared-boundary `L²` transfer-gap package obtained from an analysis and
synthesis factorization.

At every scale and Euclidean time, the actual boundary transfer is represented
as

`K_{n,t} = S_{n,t} ∘ A_{n,t}`

through an auxiliary real normed feature space.  The estimate

`‖S_{n,t}‖ * ‖A_{n,t}‖ ≤ sqrt (q(t))`

then implies the required transfer contraction by Mathlib's
`ContinuousLinearMap.opNorm_comp_le`.

This is the natural interface for the existing boundary Gram construction:
the analysis map extracts weighted open-half features and the synthesis map
reconstructs their shared-boundary moment. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate
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
  mass : ℝ
  mass_pos : 0 < mass
  quadraticDecayFactor : NNReal → ℝ
  quadraticDecayFactor_nonneg : ∀ t, 0 ≤ quadraticDecayFactor t
  slope_tendsto :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt (quadraticDecayFactor (t + t))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
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
  FeatureState : ℕ → NNReal → Type
  [featureNormedAddCommGroup : ∀ n t,
    NormedAddCommGroup (FeatureState n t)]
  [featureNormedSpace : ∀ n t,
    NormedSpace ℝ (FeatureState n t)]
  analysis :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        FeatureState n t
  synthesis :
    (n : ℕ) → (t : NNReal) →
      FeatureState n t →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (synthesis n t).comp (analysis n t)
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
      ‖synthesis n t‖ * ‖analysis n t‖ ≤
        Real.sqrt (quadraticDecayFactor t)

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate.featureNormedAddCommGroup
  PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate.featureNormedSpace

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate

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

/-- The analysis/synthesis norm product controls the norm of their composition. -/
theorem boundaryTransfer_opNorm_le
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal) :
    ‖(Q.synthesis n t).comp (Q.analysis n t)‖ ≤
      Real.sqrt (Q.quadraticDecayFactor t) :=
  ((Q.synthesis n t).opNorm_comp_le (Q.analysis n t)).trans
    (Q.factor_opNorm_mul_le n t)

/-- Convert the feature-space factorization into the direct boundary-`L²`
transfer-gap package. -/
noncomputable def toApproximatingBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  gram_integrable := Q.gram_integrable
  boundaryMoment_memLp := Q.boundaryMoment_memLp
  boundaryTransfer := fun n t =>
    (Q.synthesis n t).comp (Q.analysis n t)
  boundaryMoment_intertwining := Q.boundaryMoment_intertwining
  boundaryTransfer_opNorm_le := Q.boundaryTransfer_opNorm_le

/-- A feature-space factorization supplies the integrated boundary-moment gap
certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2TransferGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- A feature-space factorization supplies the completed finite Wilson OS
vacuum-sector norm-decay certificate. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2TransferGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate

end MathlibAnalytic
end MGAP4D

end
