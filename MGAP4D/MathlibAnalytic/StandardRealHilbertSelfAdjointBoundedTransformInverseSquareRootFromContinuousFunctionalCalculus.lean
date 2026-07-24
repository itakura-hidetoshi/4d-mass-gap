import MGAP4D.MathlibAnalytic.StandardRealHilbertSelfAdjointBoundedTransformInverseSquareRootDomainGenerated
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

/-- A generic continuous-functional-calculus package for bounded self-adjoint operators on a
real Hilbert space.

At the pinned Mathlib revision, the corresponding instance is available for complex Hilbert
spaces but not yet for arbitrary real Hilbert spaces.  Keeping it as a separate package isolates
that library-level boundary from the shifted-square construction. -/
structure RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  continuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint

/-- A real self-adjoint continuous functional calculus constructs the positive square root of any
already-generated positive bounded shifted-square inverse.

The square root is obtained from Mathlib's generic CFC square-root theorem.  Positivity of the
input follows from its self-adjointness and quadratic-form nonnegativity; positivity of the output
follows from the nonnegative-spectrum characterization under the same CFC instance. -/
noncomputable def RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData.toAlgebraicSquareRootData
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H)
    {A : H →ₗ.[ℝ] H}
    (K : StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseData A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootData K := by
  letI : ContinuousFunctionalCalculus ℝ (H →L[ℝ] H) IsSelfAdjoint :=
    C.continuousFunctionalCalculus
  letI : StarOrderedRing (H →L[ℝ] H) :=
    ContinuousLinearMap.instStarOrderedRingRCLike
  have hKPositive : K.inverse.IsPositive :=
    (ContinuousLinearMap.isPositive_iff' K.inverse).2
      ⟨K.selfAdjoint, K.quadraticForm_nonnegative⟩
  obtain ⟨R, hRSelfAdjoint, hRSpectrum, hRSquare⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
      K.selfAdjoint hKPositive.spectrumRestricts
  have hRNonnegative : 0 ≤ R :=
    nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mpr
      ⟨hRSelfAdjoint, hRSpectrum⟩
  have hRPositive : R.IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive R).mp hRNonnegative
  refine
    { squareRoot := R
      selfAdjoint := hRSelfAdjoint
      quadraticForm_nonnegative := fun x => hRPositive.inner_nonneg_left x
      squareRoot_sq := fun x => ?_ }
  have hApply := congrArg (fun T : H →L[ℝ] H => T x) hRSquare
  change R (R x) = K.inverse x at hApply
  exact hApply

/-- Uniform availability of the real-Hilbert bounded self-adjoint continuous functional calculus. -/
structure RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusDataConstructor where
  construct :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
      RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusData H

/-- A uniform real-Hilbert self-adjoint CFC package supplies the exact algebraic positive-square-root
constructor required after the shifted-square inverse has been generated. -/
def RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusDataConstructor.toAlgebraicSquareRootDataConstructor
    (C : RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusDataConstructor) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseAlgebraicSquareRootDataConstructor where
  construct := fun _A _core K => C.construct.toAlgebraicSquareRootData K

/-- The graph-Riesz bounded inverse followed by a generic real self-adjoint CFC.  This replaces the
operator-specific positive-square-root constructor by one library-level CFC boundary. -/
structure ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor where
  boundedInverse :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseDataConstructor
  continuousFunctionalCalculus :
    RealHilbertBoundedSelfAdjointContinuousFunctionalCalculusDataConstructor

/-- Collapse the CFC-factored route to the preceding natural-domain square-root factorization. -/
def ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor.toNaturalDomainSquareRootFactored
    (P : ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor) :
    NaturalDomainSquareRootFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor where
  boundedInverse := P.boundedInverse
  positiveSquareRoot :=
    P.continuousFunctionalCalculus.toAlgebraicSquareRootDataConstructor
      .toNaturalDomainSquareRootDataConstructor

/-- Apply the CFC-factored construction to one real-Hilbert self-adjoint operator. -/
def ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor.construct
    (P : ContinuousFunctionalCalculusFactoredStandardRealHilbertSelfAdjointBoundedTransformConstructor)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →ₗ.[ℝ] H)
    (core : RealHilbertSelfAdjointCore A) :
    StandardRealHilbertSelfAdjointCanonicalPositiveShiftedSquareBoundedInverseNaturalDomainSquareRootData
      (P.boundedInverse.construct A core) :=
  P.toNaturalDomainSquareRootFactored.construct A core

end

end MathlibAnalytic
end MGAP4D
