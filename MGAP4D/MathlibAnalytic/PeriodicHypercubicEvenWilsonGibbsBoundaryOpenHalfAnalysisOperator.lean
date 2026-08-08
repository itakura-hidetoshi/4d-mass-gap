import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfProductL2
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

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

local instance (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The already-constructed physical boundary/open-half Gram feature, with its
product measure exposed in the exact form required by the generic rectangular
Hilbert--Schmidt operator. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  simpa [periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
      H N hN beta hbeta)

/-- Actual compact Wilson feature-analysis operator

`A_φ : L²(boundary Haar) → L²(open-half Haar)`

obtained directly from the physical two-variable Gram feature by the generic
rectangular Fréchet--Riesz Hilbert--Schmidt construction. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
  realL2HilbertSchmidtRectangularKernelOperator
    (μ := periodicHypercubicEvenBoundaryHaarMeasure H N)
    (ν := periodicHypercubicEvenOpenHalfHaarMeasure H N)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      H N hN beta hbeta)

/-- Exact matrix coefficient of the actual Wilson boundary-to-open-half
analysis operator. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (g : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) f g := by
  exact realL2HilbertSchmidtRectangularKernelOperator_inner
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      H N hN beta hbeta) f g

/-- The analysis-operator norm is controlled by the exact physical
boundary/open-half product-`L²` norm. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_norm_le
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta‖ := by
  exact realL2HilbertSchmidtRectangularKernelOperator_norm_le
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      H N hN beta hbeta)

/-- The physical synthesis operator is the Hilbert adjoint of feature
analysis.  This keeps analysis/synthesis on the exact Mathlib Hilbert carriers
used downstream, without introducing a second pointwise kernel
representative. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
  (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta)†

/-- Analysis and adjoint synthesis have exactly the same operator norm. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_norm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta‖ := by
  simp [periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator]

/-- Exact adjoint matrix coefficient relating synthesis to analysis. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (u : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
          H N hN beta hbeta u) f =
      inner ℝ u
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H N hN beta hbeta) f u

/-- The canonical operator-level Gram factor generated by the actual Wilson
feature is `A† A`. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
  (periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
      H N hN beta hbeta).comp
    (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H N hN beta hbeta)

/-- The quadratic form of `A† A` is exactly the squared open-half feature norm. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta f) f =
      ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f‖ ^ 2 := by
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta
  change inner ℝ ((A†) (A f)) f = ‖A f‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact real_inner_self_eq_norm_sq _

/-- The canonical factorized feature operator is symmetric. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_isSymmetric
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)).IsSymmetric := by
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta
  intro f g
  change inner ℝ ((A†) (A f)) g = inner ℝ f ((A†) (A g))
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- The canonical `A† A` feature operator is positive on complete boundary
Haar `L²`. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_isPositive
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)).IsPositive := by
  rw [LinearMap.isPositive_iff]
  refine ⟨periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_isSymmetric
    H N hN beta hbeta, ?_⟩
  intro f
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self]
  exact sq_nonneg _

/-- Exact `C*` norm identity for the actual factorized feature operator. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_norm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta‖ *
        ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta‖ := by
  let A := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta
  change ‖A† ∘L A‖ = ‖A‖ * ‖A‖
  exact ContinuousLinearMap.norm_adjoint_comp_self A

/-- The norm of the factorized operator is bounded by the squared product-`L²`
feature norm. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_norm_le_feature_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta‖ ^ 2 := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_norm]
  have hA := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_norm_le
    H N hN beta hbeta
  have hA0 := norm_nonneg
    (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H N hN beta hbeta)
  have hK0 := norm_nonneg
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
      H N hN beta hbeta)
  nlinarith

/-- Audit-visible actual Wilson rectangular-analysis / adjoint-synthesis
package.  The next bridge identifies this canonical `A† A` operator with the
already-constructed shared-boundary Gram Hilbert--Schmidt operator. -/
structure PeriodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  analysisMatrixCoefficient :
    ∀ (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
      (g : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)),
      inner ℝ
          (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
            H N hN beta hbeta f) g =
        realL2HilbertSchmidtKernelPairing
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
            H N hN beta hbeta) f g
  analysisNormBound :
    ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta‖
  synthesisNormEq :
    ‖periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta‖
  factorizedPositive :
    ((periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
      H N hN beta hbeta :
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →L[ℝ]
          Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
      Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) →ₗ[ℝ]
        Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)).IsPositive
  factorizedQuadratic :
    ∀ f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N),
      inner ℝ
          (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
            H N hN beta hbeta f) f =
        ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
            H N hN beta hbeta f‖ ^ 2

/-- Construct the actual Wilson rectangular-analysis / adjoint-synthesis
receipt. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisPackage
      H N hN beta hbeta :=
  { analysisMatrixCoefficient :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
        H N hN beta hbeta
    analysisNormBound :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_norm_le
        H N hN beta hbeta
    synthesisNormEq :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureSynthesisOperator_norm
        H N hN beta hbeta
    factorizedPositive :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_isPositive
        H N hN beta hbeta
    factorizedQuadratic :=
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
