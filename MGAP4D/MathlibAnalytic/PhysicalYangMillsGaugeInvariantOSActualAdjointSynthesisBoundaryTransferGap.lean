import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentAdjointSynthesis
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingBoundaryL2FactorizedGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance actualAdjointTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualAdjointTransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualAdjointTransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualAdjointTransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualAdjointTransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualAdjointTransferSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual open-half Haar `L²` feature carrier at one approximating scale.
It is independent of Euclidean transfer time; the time dependence is carried by
the analysis map below. -/
abbrev PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2
    (halfExtent : ℕ → ℕ) (N n : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N)

/-- Canonical actual Wilson synthesis at scale `n`.  This is not an abstract
factor of the transfer certificate: it is the Hilbert adjoint `A_φ†` of the
already-constructed boundary-to-open-half Wilson feature analysis operator. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
    (halfExtent n) N hN (beta n) (hbeta n)

/-- The actual physical boundary moment, with its `L²` membership generated
internally from the finite Wilson Gram feature rather than supplied as a
certificate hypothesis. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
    S D halfExtent N hN beta hbeta B hInvariant n F
    (physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
      S D halfExtent N hN beta hbeta B hInvariant n F)

/-- Canonical boundary moments are exactly the output of the actual Wilson
adjoint synthesis on the actual positive-half observable.

This is the physical specialization of `m_u = A_φ† u`, repackaged with all
`MemLp` proofs hidden from the time-dependent transfer interface. -/
theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
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
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F =
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
          S D halfExtent N hN beta hbeta B hInvariant n F) := by
  exact
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_eq_synthesisOperator
      S D halfExtent N hN beta hbeta B hInvariant n F
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
        S D halfExtent N hN beta hbeta B hInvariant n F)

/-- Canonical time-dependent factorized boundary-transfer certificate.

Compared with the older generic factorized interface, this package removes all
routine finite-volume analytic hypotheses and fixes the synthesis factor to the
*actual* Wilson operator `A_φ†`.

The only genuinely time-dependent model input left is an analysis map

`A_{n,t} : L²(boundary) → L²(open-half)`

such that `A_φ† ∘ A_{n,t}` intertwines centered half-time translation and obeys

`‖A_φ†‖ ‖A_{n,t}‖ ≤ sqrt(q(t))`.

Thus the remaining frontier is exactly the construction and contraction of the
time-dependent analysis factor; boundary Gram integrability, boundary-moment
`L²` membership, and synthesis identification are theorem-generated. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate
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
  analysis :
    (n : ℕ) → (t : NNReal) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n
  boundaryMoment_intertwining :
    ∀ (n : ℕ) (t : NNReal),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n
      let Tn := C.toPositiveTimeObservableContractionSemigroup n
      ∀ F : Pn.Carrier,
        (physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
            halfExtent N hN beta hbeta n).comp (analysis n t)
            (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
              S D halfExtent N hN beta hbeta B hInvariant n
              (Pn.vacuumCenteredCarrier F)) =
          physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n
            (Tn.carrierTranslation (t / 2) (Pn.vacuumCenteredCarrier F))
  factor_opNorm_mul_le :
    ∀ (n : ℕ) (t : NNReal),
      ‖physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
          halfExtent N hN beta hbeta n‖ * ‖analysis n t‖ ≤
        Real.sqrt (quadraticDecayFactor t)

namespace PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate

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

/-- The actual finite Wilson Gram integrability field required by the legacy
gap certificate is automatic for every carrier element. -/
theorem gram_integrable
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) N) :
    Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        (halfExtent n) N hN (beta n) (hbeta n)
        (fun x =>
          physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
            S D halfExtent N hN beta hbeta B hInvariant n F x)
        b)
      (periodicHypercubicEvenOpenHalfHaarMeasure (halfExtent n) N) := by
  simpa using
    periodicHypercubicEvenBoundaryObservableGramFeature_integrable_of_boundedContinuous
      (halfExtent n) N hN (beta n) (hbeta n)
      (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservable
        S D halfExtent N hN beta hbeta B hInvariant n F)
      b

/-- The canonical actual-adjoint package generates the older generic
analysis/synthesis factorized certificate without adding any analytic
hypothesis. -/
noncomputable def toApproximatingBoundaryL2FactorizedGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := Q.mass
  mass_pos := Q.mass_pos
  quadraticDecayFactor := Q.quadraticDecayFactor
  quadraticDecayFactor_nonneg := Q.quadraticDecayFactor_nonneg
  slope_tendsto := Q.slope_tendsto
  exchange := Q.exchange
  gram_integrable := gram_integrable
  boundaryMoment_memLp :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
      S D halfExtent N hN beta hbeta B hInvariant
  FeatureState := fun n _ =>
    PhysicalYangMillsEvenPeriodicWilsonOSOpenHalfFeatureL2 halfExtent N n
  featureNormedAddCommGroup := fun _ _ => inferInstance
  featureNormedSpace := fun _ _ => inferInstance
  analysis := Q.analysis
  synthesis := fun n _ =>
    physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
      halfExtent N hN beta hbeta n
  boundaryMoment_intertwining := by
    intro n t
    dsimp only
    intro F
    exact Q.boundaryMoment_intertwining n t F
  factor_opNorm_mul_le := Q.factor_opNorm_mul_le

/-- The actual-adjoint factorization yields the direct boundary-`L²` transfer
certificate and hence its operator-norm contraction. -/
noncomputable def toApproximatingBoundaryL2TransferGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2FactorizedGapCertificate
    |>.toApproximatingBoundaryL2TransferGapCertificate

/-- The actual-adjoint factorization yields the integrated boundary-moment gap
certificate. -/
noncomputable def toApproximatingBoundaryMomentGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingBoundaryMomentGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2TransferGapCertificate
    |>.toApproximatingBoundaryMomentGapCertificate

/-- The actual-adjoint factorization yields the complete finite Wilson OS
vacuum-sector gap certificate used by the continuum Hamiltonian route. -/
noncomputable def toApproximatingVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C :=
  Q.toApproximatingBoundaryL2TransferGapCertificate
    |>.toApproximatingVacuumGapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate

end MathlibAnalytic
end MGAP4D

end