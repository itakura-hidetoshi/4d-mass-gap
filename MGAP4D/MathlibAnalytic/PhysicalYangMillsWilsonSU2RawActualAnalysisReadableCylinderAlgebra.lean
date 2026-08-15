import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadableSubalgebra
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisContinuousPullbackClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem rawActualAnalysisReadableCylinderAlgebraTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance rawActualAnalysisReadableCylinderAlgebraNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rawActualAnalysisReadableCylinderAlgebraTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance rawActualAnalysisReadableCylinderAlgebraCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance rawActualAnalysisReadableCylinderAlgebraSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance rawActualAnalysisReadableCylinderAlgebraMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance rawActualAnalysisReadableCylinderAlgebraBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance rawActualAnalysisReadableCylinderAlgebraSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev rawActualAnalysisReadableCylinderAlgebraPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 rawActualAnalysisReadableCylinderAlgebraTwoRankPositive beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2 rawActualAnalysisReadableCylinderAlgebraTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- If the explicit raw actual-Wilson mode is a uniform limit of readable
positive-half cylinder targets, then it lies in the coherent positive-half
pullback range closure.

The readable algebra already packages genuine observables in
`D.positiveTimeSubalgebra`; this theorem only applies the previously proved
subalgebra-closure inclusion.  No global density, surjectivity, or
multiplicativity of `positiveHalfPullback` is used. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_mem_positiveHalfCylinderReadableSubalgebraClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 rawActualAnalysisReadableCylinderAlgebraTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hReadable :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) k c ∈
        closure
          (↑(positiveHalfCylinderReadableSubalgebra Q n) :
            Set (BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  exact
    (Q.closure_positiveHalfCylinderReadableSubalgebra_subset_positiveHalfPullbackRangeClosure
      C hInvariant U n) hReadable

/-- Generator-level version of the preceding theorem.  It is enough to realize
a chosen set of positive-half cylinder generators physically and approximate
the raw actual-Wilson target uniformly by their real algebraic closure.

Thus a model-facing proof may work generator-by-generator and then use
`Algebra.adjoin`; it need not lift the whole actual plaquette algebra as a
primitive object. -/
theorem
    normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_mem_closure_algebraAdjoin_readableCylinders
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 rawActualAnalysisReadableCylinderAlgebraTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (s : Set (BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
        (halfExtent n) 2) ℝ))
    (hs : s ⊆
      (↑(positiveHalfCylinderReadableSubalgebra Q n) :
        Set (BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) 2) ℝ)))
    (hAdjoin :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) k c ∈
        closure
          (↑(Algebra.adjoin ℝ s) :
            Set (BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ))) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) k c ∈
      closure (LinearMap.range (Q.positiveHalfPullback n)) := by
  exact
    (Q.closure_algebraAdjoin_subset_positiveHalfPullbackRangeClosure
      C hInvariant U n s hs) hAdjoin

/-- Terminal reconstructed-Hamiltonian consequence of uniform approximation by
readable cylinder targets.  The only new premise compared with the existing
raw-actual-analysis endpoint is the concrete `C⁰` membership in the closure of
the readable cylinder algebra; the transfer to `L²` and the physical mass
inequality are theorem-generated downstream. -/
theorem
    normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_mem_positiveHalfCylinderReadableSubalgebraClosure
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 rawActualAnalysisReadableCylinderAlgebraTwoRankPositive beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hH : 1 < halfExtent n)
    (hbetaPos : 0 < beta n)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (periodicHypercubicEvenBoundaryMarginalVacuumL2
          (halfExtent n) (beta n) (hbeta n))
        (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
          (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hReadable :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisBoundedContinuousFunction
          (halfExtent n) (beta n) (hbeta n) k c ∈
        closure
          (↑(positiveHalfCylinderReadableSubalgebra Q n) :
            Set (BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ)))
    (T : (rawActualAnalysisReadableCylinderAlgebraPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  apply
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure
      hInvariant U n k c hH hbetaPos hc hzero _ T hSelf
  exact
    Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveHalfPullbackRangeClosure_of_mem_positiveHalfCylinderReadableSubalgebraClosure
      C hInvariant U n k c hReadable

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
