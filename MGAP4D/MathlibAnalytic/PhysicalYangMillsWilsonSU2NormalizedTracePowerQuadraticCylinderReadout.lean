import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveHalfQuadraticPolarization
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerQuadraticCylinderReadoutTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerQuadraticCylinderReadoutSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The canonical unit in the positive-time observable submodule, exposed here
so target-specific quadratic readout data can state unit normalization without
referring to the private helper used inside the polarization proof. -/
def physicalYangMillsWilsonSU2PositiveTimeUnit
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S} :
    D.positiveTimeSubalgebra.toSubmodule :=
  ⟨(1 : physicalYangMillsGaugeInvariantObservableSubalgebra S),
    D.positiveTimeSubalgebra.one_mem⟩

/-- Shift a positive-time observable by the algebra unit while retaining the
positive-time certificate.  This is definitionally the shift used by the
quadratic-polarization theorem. -/
def physicalYangMillsWilsonSU2PositiveTimeAddOne
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (F : D.positiveTimeSubalgebra) : D.positiveTimeSubalgebra :=
  ⟨(F : physicalYangMillsGaugeInvariantObservableSubalgebra S) +
      (1 : physicalYangMillsGaugeInvariantObservableSubalgebra S),
    D.positiveTimeSubalgebra.add_mem F.2 D.positiveTimeSubalgebra.one_mem⟩

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- For one explicit normalized-trace-power raw mode, two concrete reflected
cylinder identities determine the exact coherent positive-half readout.

The first identity is for `F`; the second is for `F + 1`.  Scalar quadratic
polarization then removes the sign ambiguity of a rank-one reflected product.
No multiplicativity or surjectivity of the coherent pullback is assumed. -/
theorem normalizedTracePower_positiveHalfPullback_eq_of_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerQuadraticCylinderReadoutTwoRankPositive
        beta hbeta)
    (n j : ℕ)
    (hUnit :
      Q.positiveHalfPullback n
          (physicalYangMillsWilsonSU2PositiveTimeUnit (S := S) (D := D)) =
        (1 : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) 2) ℝ))
    (F : D.positiveTimeSubalgebra)
    (hQuadratic : ∀ A,
      D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A)
    (hQuadraticAddOne : ∀ A,
      D.quadraticBoundedContinuousFunction
          (physicalYangMillsWilsonSU2PositiveTimeAddOne (D := D) F)
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
              (halfExtent n) (beta n) (hbeta n) j +
            (1 : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ)) A) :
    Q.positiveHalfPullback n
        (⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule) =
      periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j := by
  exact Q.positiveHalfPullback_eq_of_quadratic_polarization
    n hUnit F
      (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j)
      hQuadratic hQuadraticAddOne

/-- The same target-specific quadratic cylinder data gives exact range
membership, with the physical observable itself as the preimage. -/
theorem normalizedTracePower_rawBounded_mem_positiveHalfPullbackRange_of_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerQuadraticCylinderReadoutTwoRankPositive
        beta hbeta)
    (n j : ℕ)
    (hUnit :
      Q.positiveHalfPullback n
          (physicalYangMillsWilsonSU2PositiveTimeUnit (S := S) (D := D)) =
        (1 : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) 2) ℝ))
    (F : D.positiveTimeSubalgebra)
    (hQuadratic : ∀ A,
      D.quadraticBoundedContinuousFunction F (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A)
    (hQuadraticAddOne : ∀ A,
      D.quadraticBoundedContinuousFunction
          (physicalYangMillsWilsonSU2PositiveTimeAddOne (D := D) F)
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
              (halfExtent n) (beta n) (hbeta n) j +
            (1 : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ)) A) :
    periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
        (halfExtent n) (beta n) (hbeta n) j ∈
      LinearMap.range (Q.positiveHalfPullback n) := by
  refine ⟨(⟨F.1, F.2⟩ : D.positiveTimeSubalgebra.toSubmodule), ?_⟩
  exact Q.normalizedTracePower_positiveHalfPullback_eq_of_quadraticCylinder
    n j hUnit F hQuadratic hQuadraticAddOne

/-- A family of physical positive-time observables satisfying the two reflected
cylinder identities for every normalized-trace power constructs the existing
readout package.  Thus the readout package is reduced to explicit cylinder
identities rather than a range or density assumption. -/
noncomputable def normalizedTracePowerPositiveTimeReadout_of_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerQuadraticCylinderReadoutTwoRankPositive
        beta hbeta)
    (n : ℕ)
    (hUnit :
      Q.positiveHalfPullback n
          (physicalYangMillsWilsonSU2PositiveTimeUnit (S := S) (D := D)) =
        (1 : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) 2) ℝ))
    (F : ℕ → D.positiveTimeSubalgebra)
    (hQuadratic : ∀ j A,
      D.quadraticBoundedContinuousFunction (F j) (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A)
    (hQuadraticAddOne : ∀ j A,
      D.quadraticBoundedContinuousFunction
          (physicalYangMillsWilsonSU2PositiveTimeAddOne (D := D) (F j))
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
              (halfExtent n) (beta n) (hbeta n) j +
            (1 : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ)) A) :
    PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveTimeReadout Q n :=
  { observable := fun j =>
      (⟨(F j).1, (F j).2⟩ : D.positiveTimeSubalgebra.toSubmodule)
    positiveHalfPullback_eq := fun j =>
      Q.normalizedTracePower_positiveHalfPullback_eq_of_quadraticCylinder
        n j hUnit (F j) (hQuadratic j) (hQuadraticAddOne j) }

/-- The quadratic-cylinder realization therefore places every normalized-trace
polynomial raw actual-analysis vector in the exact physical positive-time
`L²` range by the already-proved finite linearity theorem. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 normalizedTracePowerQuadraticCylinderReadoutTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hUnit :
      Q.positiveHalfPullback n
          (physicalYangMillsWilsonSU2PositiveTimeUnit (S := S) (D := D)) =
        (1 : BoundedContinuousFunction
          (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
            (halfExtent n) 2) ℝ))
    (F : ℕ → D.positiveTimeSubalgebra)
    (hQuadratic : ∀ j A,
      D.quadraticBoundedContinuousFunction (F j) (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
            (halfExtent n) (beta n) (hbeta n) j) A)
    (hQuadraticAddOne : ∀ j A,
      D.quadraticBoundedContinuousFunction
          (physicalYangMillsWilsonSU2PositiveTimeAddOne (D := D) (F j))
          (Q.interpolate n A) =
        periodicHypercubicEvenFullReflectedObservable (halfExtent n)
          (periodicHypercubicEvenBoundaryNormalizedTracePowerRawActualAnalysisBoundedContinuousFunction
              (halfExtent n) (beta n) (hbeta n) j +
            (1 : BoundedContinuousFunction
              (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
                (halfExtent n) 2) ℝ)) A) :
    periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
      LinearMap.range (Q.positiveTimeSubmoduleL2LinearMap n) := by
  let R := Q.normalizedTracePowerPositiveTimeReadout_of_quadraticCylinder
    n hUnit F hQuadratic hQuadraticAddOne
  exact Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_readout
    hInvariant n k c R

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
