import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerQuadraticCylinderReadout
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryMarginalVacuumNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerQuadraticCylinderVacuumNormalizedSU2Nontrivial :
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

private abbrev normalizedTracePowerQuadraticCylinderVacuumNormalizedPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2
      normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- The unit normalization used by quadratic polarization is already contained
in the existing OS vacuum-unit compatibility.  The apparent extra `hUnit`
premise of the target-specific readout theorem is therefore not a new model
assumption. -/
theorem positiveHalfPullback_positiveTimeUnit_eq_one_of_vacuumCompatibility
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ) :
    Q.positiveHalfPullback n
        (physicalYangMillsWilsonSU2PositiveTimeUnit (S := S) (D := D)) =
      (1 : BoundedContinuousFunction
        (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration
          (halfExtent n) 2) ℝ) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent 2
        normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
        beta hbeta Q.toWeakStarBridge hInvariant n
  have hCarrierUnit :
      Pn.toPositiveTime Pn.vacuumObservable =
        physicalYangMillsWilsonSU2PositiveTimeUnit (S := S) (D := D) := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [← hCarrierUnit]
  simpa [Pn] using U.positiveHalfPullback_vacuum_eq_one n

/-- After using the already-established vacuum compatibility, the exact
normalized-trace-power readout requires only the two concrete reflected
cylinder identities for `F` and `F + 1`. -/
theorem normalizedTracePower_positiveHalfPullback_eq_of_vacuumCompatibility_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n j : ℕ)
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
  exact Q.normalizedTracePower_positiveHalfPullback_eq_of_quadraticCylinder
    n j
      (Q.positiveHalfPullback_positiveTimeUnit_eq_one_of_vacuumCompatibility
        hInvariant U n)
      F hQuadratic hQuadraticAddOne

/-- A family of concrete trace-power cylinder identities, together with the
already-used vacuum compatibility, constructs the reusable positive-time
readout package with no separate unit or range hypothesis. -/
noncomputable def
    normalizedTracePowerPositiveTimeReadout_of_vacuumCompatibility_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n : ℕ)
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
  Q.normalizedTracePowerPositiveTimeReadout_of_quadraticCylinder
    n
      (Q.positiveHalfPullback_positiveTimeUnit_eq_one_of_vacuumCompatibility
        hInvariant U n)
      F hQuadratic hQuadraticAddOne

/-- Hence the two cylinder identities alone (after theorem-generated vacuum
normalization) place every normalized-trace polynomial raw actual-analysis
vector in the exact physical positive-time `L²` range. -/
theorem normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_vacuumCompatibility_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
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
  exact Q.normalizedTracePolynomial_rawActualAnalysis_mem_positiveTimeL2Range_of_quadraticCylinder
    hInvariant n k c
      (Q.positiveHalfPullback_positiveTimeUnit_eq_one_of_vacuumCompatibility
        hInvariant U n)
      F hQuadratic hQuadraticAddOne

/-- The same concrete cylinder identities feed directly into the reconstructed
Hamiltonian variational route.  This endpoint adds no range, density, unit,
multiplicativity, or surjectivity premise beyond the already-existing vacuum
compatibility. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_vacuumCompatibility_quadraticCylinder
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerQuadraticCylinderVacuumNormalizedTwoRankPositive
        beta hbeta)
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
                (halfExtent n) 2) ℝ)) A)
    (T : (normalizedTracePowerQuadraticCylinderVacuumNormalizedPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  let R :=
    Q.normalizedTracePowerPositiveTimeReadout_of_vacuumCompatibility_quadraticCylinder
      hInvariant U n F hQuadratic hQuadraticAddOne
  exact Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_readout
    hInvariant U n k c hH hbetaPos hc hzero R T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
