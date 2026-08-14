import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfAnalysisOperator
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasureInstances
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelGramFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance boundaryGramFactorizationSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryGramFactorizationSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryGramFactorizationSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryGramFactorizationSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryGramFactorizationSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryGramFactorizationSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance boundaryGramFactorizationBoundaryHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance boundaryGramFactorizationOpenHalfHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The Wilson-specific `A†A` operator is definitionally the generic Gram
factor of the actual completed positive boundary/open-half Hilbert--Schmidt
kernel.  This theorem exposes that identification to downstream files without
re-unfolding the Wilson analysis/synthesis stack. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_eq_generic
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H N hN beta hbeta =
      realL2HilbertSchmidtRectangularKernelFactorizedOperator
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) := by
  rfl

/-- Exact weak Gram identity for the actual Wilson analysis operator.

For arbitrary boundary `L²` vectors `f,g`, the matrix coefficient of the
physical factorized operator `A†A` is the open-half Hilbert inner product of
the two actual analyzed vectors. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta g) := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_eq_generic]
  exact
    realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta) f g

/-- The same Wilson Gram coefficient written directly as the original
rectangular Hilbert--Schmidt kernel pairing.  This is the exact handoff point
for identifying `A†A` with the shared-boundary square Gram kernel using the
already-proved open-half integral formula. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_eq_kernelPairing
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta)
        f
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta g) := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_eq_generic]
  exact
    realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_eq_pairing
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta) f g

/-- Cancellation-free strictness criterion for the actual Wilson analysis:
the Wilson `A†A` quadratic form is strictly positive exactly when the analyzed
open-half vector is nonzero. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self_pos_iff_analysis_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    0 < inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
          H N hN beta hbeta f) f ↔
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f ≠ 0 := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_eq_generic]
  exact
    realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_self_pos_iff
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta) f

end

end MathlibAnalytic
end MGAP4D
