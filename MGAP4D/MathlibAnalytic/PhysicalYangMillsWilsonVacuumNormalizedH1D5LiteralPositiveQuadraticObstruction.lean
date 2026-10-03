import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5RankOneTransferObstruction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferRawIntegral
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import Mathlib.Tactic

/-!
# Literal positive-quadratic obstruction to vacuum-normalized H1-D5

#5041 shows that H1-D5 forces the actual finite physical one-slab transfer to
be rank one along the normalized top vector.

Therefore every vector in the full top-eigenspace orthogonal complement must be
annihilated by the raw one-slab transfer.  This file exposes the same statement
in two model-facing scalar forms:

1. the diagonal physical transfer coefficient must vanish;
2. the literal finite Wilson double integral for that coefficient must vanish.

The existing physical feature factorization gives a third equivalent
obstruction surface:

  `<T f,f> = ||A f||^2`.

Hence any top-orthogonal physical vector with nonzero one-slab feature-analysis
image theorem-generates a strictly positive literal Wilson quadratic form and
refutes H1-D5.

No new spectral, compatibility, or continuum assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5LiteralPosTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5LiteralPosCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5LiteralPosSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5LiteralPosMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5LiteralPosBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5LiteralPosSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5LiteralPosPhysicalSliceComplete (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- A full-top-orthogonal physical vector has zero overlap with the chosen
normalized top vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_inner_topOrthogonal_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
          H N hN beta hbeta)
        (f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N) = 0 := by
  have hf := f.property
  change
    (f :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
        H N) ∈
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        H N hN beta hbeta)ᗮ at hf
  rw [Submodule.mem_orthogonal] at hf
  exact
    hf
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
        H N hN beta hbeta)

section PhysicalWilsonH1D5LiteralPositiveQuadratic

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- H1-D5 forces every full-top-orthogonal physical vector to have zero raw
one-slab quadratic coefficient. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonal_rawQuadratic_eq_zero
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ)
    (f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)
          (f :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N))
        (f :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N) = 0 := by
  let H := halfExtent n
  let G :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
  let T : G →L[ℝ] G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN (beta n) (hbeta n)
  let Omega : G :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN (beta n) (hbeta n)
  let P : G →L[ℝ] G :=
    InnerProductSpace.rankOne ℝ Omega Omega
  have hRank :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_physicalOneSlabTransfer_norm_smul_rankOne
      Q hInvariant C hCompat n
  have hfOmega :
      inner ℝ Omega (f : G) = 0 := by
    simpa only [H, G, Omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_inner_topOrthogonal_eq_zero
        H N hN (beta n) (hbeta n) f
  have hApply :=
    congrArg
      (fun A : G →L[ℝ] G => A (f : G))
      hRank
  change
    T (f : G) =
      (‖T‖ • P) (f : G) at hApply
  have hTf : T (f : G) = 0 := by
    rw [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
      hfOmega, zero_smul, smul_zero] at hApply
    exact hApply
  change inner ℝ (T (f : G)) (f : G) = 0
  rw [hTf, inner_zero_left]

/-- Exact literal finite-Wilson form of the preceding forced vanishing. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonal_literalWilsonQuadratic_eq_zero
    (hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C)
    (n : ℕ)
    (f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    (∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
            (halfExtent n) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
            (halfExtent n) N,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          (halfExtent n) N (beta n) p.1 p.2 *
        (((f :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N) :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                (halfExtent n) N)) p.1 *
          ((f :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N) :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                (halfExtent n) N)) p.2)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
        (halfExtent n) N)) = 0 := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_rawIntegral]
  exact
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonal_rawQuadratic_eq_zero
      Q hInvariant C hCompat n f

/-- Any strictly positive top-orthogonal literal Wilson one-slab quadratic
integral refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_topOrthogonal_literalWilsonQuadratic_pos
    (n : ℕ)
    (f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n))
    (hpos :
      0 <
        ∫ p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
                (halfExtent n) N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
                (halfExtent n) N,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              (halfExtent n) N (beta n) p.1 p.2 *
            (((f :
                periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                  (halfExtent n) N) :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    (halfExtent n) N)) p.1 *
              ((f :
                periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                  (halfExtent n) N) :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    (halfExtent n) N)) p.2)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
            (halfExtent n) N)) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  intro hCompat
  have hzero :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonal_literalWilsonQuadratic_eq_zero
      Q hInvariant C hCompat n f
  linarith

/-- The feature-analysis form of the same obstruction: a single top-orthogonal
physical vector which survives one-slab feature analysis refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_topOrthogonal_featureAnalysis_ne_zero
    (n : ℕ)
    (f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n))
    (hA :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          (halfExtent n) N hN (beta n) (hbeta n)
          (f :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N) ≠ 0) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  intro hCompat
  have hzero :=
    physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonal_rawQuadratic_eq_zero
      Q hInvariant C hCompat n f
  have hquad :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_quadratic_eq_analysis_norm_sq
      (halfExtent n) N hN (beta n) (hbeta n)
      (f :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (halfExtent n) N)
  have hnormPos :
      0 <
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (f :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                (halfExtent n) N)‖ :=
    norm_pos_iff.mpr hA
  have hsquarePos :
      0 <
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (f :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                (halfExtent n) N)‖ ^ 2 :=
    sq_pos_of_pos hnormPos
  rw [hzero] at hquad
  linarith

/-- Audit-visible exact finite-model obstruction package. -/
structure PhysicalYangMillsVacuumNormalizedH1D5LiteralPositiveQuadraticObstructionPackage : Prop where
  compatibilityForcesLiteralZero :
    ∀ (_hCompat :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C),
      ∀ n : ℕ,
        ∀ f :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            (halfExtent n) N hN (beta n) (hbeta n),
          inner ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
                (halfExtent n) N hN (beta n) (hbeta n)
                (f :
                  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                    (halfExtent n) N))
              (f :
                periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                  (halfExtent n) N) = 0
  featureSurvivalObstructs :
    ∀ n : ℕ,
      ∀ f :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          (halfExtent n) N hN (beta n) (hbeta n),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            (halfExtent n) N hN (beta n) (hbeta n)
            (f :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                (halfExtent n) N) ≠ 0 →
          ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := N) (hN := hN)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C

theorem physicalYangMillsVacuumNormalizedH1D5LiteralPositiveQuadraticObstructionPackage :
    PhysicalYangMillsVacuumNormalizedH1D5LiteralPositiveQuadraticObstructionPackage
      (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { compatibilityForcesLiteralZero := by
      intro hCompat n f
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_completedCompatibility_implies_topOrthogonal_rawQuadratic_eq_zero
          Q hInvariant C hCompat n f
    featureSurvivalObstructs := by
      intro n f hA
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_topOrthogonal_featureAnalysis_ne_zero
          Q hInvariant C n f hA }

end PhysicalWilsonH1D5LiteralPositiveQuadratic

end

end MathlibAnalytic
end MGAP4D
