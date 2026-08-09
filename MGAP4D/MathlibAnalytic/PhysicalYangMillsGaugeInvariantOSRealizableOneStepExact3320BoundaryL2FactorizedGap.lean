import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableBoundaryL2GeometricDirichletGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableExact3320BoundaryDirichletEnergy
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance realizableOneStepBoundaryL2FactorizedSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance realizableOneStepBoundaryL2FactorizedSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance realizableOneStepBoundaryL2FactorizedSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance realizableOneStepBoundaryL2FactorizedSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance realizableOneStepBoundaryL2FactorizedSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance realizableOneStepBoundaryL2FactorizedSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- One-lattice-step exact `33/20` Wilson gap data factored through an
intermediate real normed feature space.

This is the realizable-time analogue of the older all-real factorized boundary
API, but it contains only the single physical lattice step.  The actual
boundary transfer is theorem-generated as

`Kₙ = synthesisₙ ∘ analysisₙ`,

and its strict norm estimate follows from Mathlib's `opNorm_comp_le` together
with the sole quantitative factor bound

`‖synthesisₙ‖ * ‖analysisₙ‖ ≤ exp (-(33/20) aₙ)`.

No finite all-real-time semigroup is introduced. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  boundaryMoment_memLp :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      MemLp
        (fun b =>
          physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n F b)
        2
        (periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)
  FeatureState : ℕ → Type
  [featureNormedAddCommGroup : ∀ n, NormedAddCommGroup (FeatureState n)]
  [featureNormedSpace : ∀ n, NormedSpace ℝ (FeatureState n)]
  analysis :
    (n : ℕ) →
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        FeatureState n
  synthesis :
    (n : ℕ) → FeatureState n →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  boundaryMoment_factorized_intertwining :
    ∀ (n : ℕ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier),
      let Pn :=
        physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
      (synthesis n).comp (analysis n)
          (physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
            (Pn.vacuumCenteredCarrier F)
            (boundaryMoment_memLp n (Pn.vacuumCenteredCarrier F))) =
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
          (R.realizableCarrierTranslation hInvariant n 1
            (Pn.vacuumCenteredCarrier F))
          (boundaryMoment_memLp n
            (R.realizableCarrierTranslation hInvariant n 1
              (Pn.vacuumCenteredCarrier F)))
  factor_opNorm_mul_le :
    ∀ n : ℕ,
      ‖synthesis n‖ * ‖analysis n‖ ≤
        physicalYangMillsExact3320OneStepNormFactor S n

attribute [instance]
  PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate.featureNormedAddCommGroup
  PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate.featureNormedSpace

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The theorem-generated shared-boundary transfer is the factor composition. -/
noncomputable def boundaryTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  (A.synthesis n).comp (A.analysis n)

/-- Mathlib's operator norm submultiplicativity turns the factor norm product
bound into the exact one-step boundary transfer bound. -/
theorem boundaryTransfer_opNorm_le
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    ‖A.boundaryTransfer n‖ ≤ physicalYangMillsExact3320OneStepNormFactor S n := by
  exact ((A.synthesis n).opNorm_comp_le (A.analysis n)).trans
    (A.factor_opNorm_mul_le n)

/-- A factorized one-step boundary estimate reconstructs the direct boundary
`L²` transfer certificate of #1490. -/
noncomputable def toBoundaryL2TransferGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2TransferGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundaryMoment_memLp := A.boundaryMoment_memLp
  boundaryTransfer := A.boundaryTransfer
  boundaryMoment_intertwining := by
    intro n F
    exact A.boundaryMoment_factorized_intertwining n F
  boundaryTransfer_opNorm_le := A.boundaryTransfer_opNorm_le

/-- Consequently the factorized one-step input generates the literal compact
Haar boundary Poincaré/Dirichlet certificate. -/
noncomputable def toBoundaryDirichletGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320BoundaryDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toBoundaryL2TransferGapCertificate.toGeometricDirichletGapCertificate
    |>.toBoundaryDirichletGapCertificate

/-- The same factorized data directly generates the exact geometric Euclidean
Dirichlet coercivity certificate. -/
noncomputable def toGeometricDirichletGapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableExact3320GeometricDirichletGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toBoundaryL2TransferGapCertificate.toGeometricDirichletGapCertificate

/-- And therefore it recovers the exact centered one-step OS norm certificate
used by the entire discrete/floor continuum gap spine. -/
noncomputable def toOneStepExact3320GapCertificate
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant :=
  A.toBoundaryL2TransferGapCertificate.toOneStepExact3320GapCertificate

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320BoundaryL2FactorizedGapCertificate

end MathlibAnalytic
end MGAP4D

end
