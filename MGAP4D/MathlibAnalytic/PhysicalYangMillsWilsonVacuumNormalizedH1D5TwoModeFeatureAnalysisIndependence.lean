import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeWilsonGramDeterminant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import Mathlib.Tactic

/-!
# H1-D5 as linear dependence of two concrete one-slab feature images

#5043 reduces H1-D5 to vanishing of the literal 2 x 2 Wilson one-slab
determinant for the explicit primary-spatial-plaquette two-mode physical family.

The physical one-slab transfer is exactly the Gram operator `A† A`.
Therefore those four matrix coefficients are the Gram matrix of the two feature
vectors `A f₀` and `A f₁`.

This file identifies the #5043 literal determinant with that actual
feature-space Gram determinant and applies Mathlib's
`Matrix.det_gram_ne_zero_iff_linearIndependent`.

Hence the remaining model-facing obstruction is simply:

  the two concrete one-slab feature-analysis images are linearly independent.

No OS completion, continuum limit, top-vector coordinate, or spectral
assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance h1d5TwoModeFeatureTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5TwoModeFeatureCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5TwoModeFeatureSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5TwoModeFeatureMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5TwoModeFeatureBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5TwoModeFeatureSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The two actual one-slab feature-analysis images of the explicit physical
primary-spatial-plaquette modes. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i : Fin 2) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
      H N hN beta hbeta).FeatureHilbert :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
      H N hN beta hbeta
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 i)

/-- The #5043 literal coefficient is exactly the feature-space inner product
of the two corresponding one-slab analysis images. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient_eq_featureAnalysis_inner
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i j : Fin 2) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
        H N hN hN2 beta hbeta i j =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
          H N hN hN2 beta hbeta i)
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
          H N hN hN2 beta hbeta j) := by
  rw [←
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysical_transferInner_eq_literalOneSlabCoefficient
      H N hN hN2 beta hbeta i j]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_analysis
      H N hN beta hbeta
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2 H hN2 i)
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2 H hN2 j)

/-- The actual 2 x 2 feature-space Gram matrix of the two explicit one-slab
analysis images. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.gram ℝ
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
      H N hN hN2 beta hbeta)

/-- Entrywise, the feature-space Gram matrix is the literal one-slab Wilson
coefficient matrix from #5043. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix_apply
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i j : Fin 2) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix
        H N hN hN2 beta hbeta i j =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient
        H N hN hN2 beta hbeta i j := by
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix
  rw [Matrix.gram_apply]
  symm
  exact
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabCoefficient_eq_featureAnalysis_inner
      H N hN hN2 beta hbeta i j

/-- The #5043 literal determinant is exactly the determinant of the actual
feature-space Gram matrix. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet_eq_featureAnalysisGramMatrix_det
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
        H N hN hN2 beta hbeta =
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix
        H N hN hN2 beta hbeta).det := by
  unfold periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
  rw [Matrix.det_fin_two]
  rw [
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix_apply
      H N hN hN2 beta hbeta 0 0,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix_apply
      H N hN hN2 beta hbeta 1 1,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix_apply
      H N hN hN2 beta hbeta 0 1,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisGramMatrix_apply
      H N hN hN2 beta hbeta 1 0
  ]

/-- The literal two-mode Wilson determinant is nonzero exactly when the two
actual one-slab feature-analysis images are linearly independent. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet_ne_zero_iff_featureAnalysis_linearIndependent
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
        H N hN hN2 beta hbeta ≠ 0 ↔
      LinearIndependent ℝ
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
          H N hN hN2 beta hbeta) := by
  rw [
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet_eq_featureAnalysisGramMatrix_det
      H N hN hN2 beta hbeta]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent

section H1D5TwoModeFeatureIndependence

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- Linear independence of the two explicit one-slab feature images at one
finite scale refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_twoModePhysicalFeatureAnalysis_linearIndependent
    (n : ℕ)
    (hLI :
      LinearIndependent ℝ
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
          (halfExtent n) N hN hN2 (beta n) (hbeta n))) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  apply
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_literalTwoModeWilsonGramDet_ne_zero
      (hN2 := hN2) Q hInvariant C n
  exact
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet_ne_zero_iff_featureAnalysis_linearIndependent
      (halfExtent n) N hN hN2 (beta n) (hbeta n)).2 hLI

/-- Audit-visible package for the exact feature-space residual. -/
structure PhysicalYangMillsVacuumNormalizedH1D5TwoModeFeatureAnalysisIndependencePackage : Prop where
  literalDeterminantIffIndependent :
    ∀ n : ℕ,
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet
          (halfExtent n) N hN hN2 (beta n) (hbeta n) ≠ 0 ↔
        LinearIndependent ℝ
          (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
            (halfExtent n) N hN hN2 (beta n) (hbeta n))
  independentFeatureImagesObstruct :
    ∀ n : ℕ,
      LinearIndependent ℝ
          (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalFeatureAnalysisImage
            (halfExtent n) N hN hN2 (beta n) (hbeta n)) →
        ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C

theorem physicalYangMillsVacuumNormalizedH1D5TwoModeFeatureAnalysisIndependencePackage :
    PhysicalYangMillsVacuumNormalizedH1D5TwoModeFeatureAnalysisIndependencePackage
      (hN2 := hN2) (Q := Q) (hInvariant := hInvariant) (C := C) :=
  { literalDeterminantIffIndependent := by
      intro n
      exact
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalLiteralOneSlabGramDet_ne_zero_iff_featureAnalysis_linearIndependent
          (halfExtent n) N hN hN2 (beta n) (hbeta n)
    independentFeatureImagesObstruct := by
      intro n hLI
      exact
        physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_twoModePhysicalFeatureAnalysis_linearIndependent
          (hN2 := hN2) Q hInvariant C n hLI }

end H1D5TwoModeFeatureIndependence

end

end MathlibAnalytic
end MGAP4D
