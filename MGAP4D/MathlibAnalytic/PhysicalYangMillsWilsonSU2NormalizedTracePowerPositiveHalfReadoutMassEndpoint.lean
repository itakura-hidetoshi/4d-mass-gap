import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerReflectionCylinderReadout
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerPositiveHalfReadoutMassEndpointTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerPositiveHalfReadoutMassEndpointNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerPositiveHalfReadoutMassEndpointTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerPositiveHalfReadoutMassEndpointCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerPositiveHalfReadoutMassEndpointSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerPositiveHalfReadoutMassEndpointMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerPositiveHalfReadoutMassEndpointBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerPositiveHalfReadoutMassEndpointSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The non-realization hypotheses already consumed by the reconstructed
Hamiltonian variational endpoint, packaged separately from the positive-time
cylinder realization.  This is only an API package: it adds no new condition. -/
structure PhysicalYangMillsWilsonSU2NormalizedTracePolynomialMassInput
    (halfExtent : ℕ → ℕ)
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ) : Prop where
  halfExtent_gt_one : 1 < halfExtent n
  beta_pos : 0 < beta n
  coefficient_ne_zero : c ≠ 0
  vacuum_orthogonal :
    inner ℝ
      (periodicHypercubicEvenBoundaryMarginalVacuumL2
        (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
        (halfExtent n) (beta n) (hbeta n) k c) = 0

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

private abbrev normalizedTracePowerPositiveHalfReadoutMassEndpointPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerPositiveHalfReadoutMassEndpointTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2
      normalizedTracePowerPositiveHalfReadoutMassEndpointTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- Terminal finite-scale consequence of the reduced realization interface.

Once interpolation respects physical reflection, one pointwise positive-half
trace-power cylinder readout per power is enough.  Reflection supplies the
negative half, algebraic polarization supplies the two quadratic identities,
vacuum compatibility supplies the unit, and the existing actual-analysis / OS
route supplies the exact `L²` range realization and reconstructed Hamiltonian
variational mass conclusion.

No whole-algebra lift, density, global pullback surjectivity, multiplicativity,
or new Hamiltonian assumption appears here. -/
theorem normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_vacuumCompatibility_positiveHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerPositiveHalfReadoutMassEndpointTwoRankPositive
        beta hbeta)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSInterpolationReflectionCompatibility Q)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (M : PhysicalYangMillsWilsonSU2NormalizedTracePolynomialMassInput
      halfExtent beta hbeta n k c)
    (R : NormalizedTracePowerPositiveHalfReadoutFamily Q n)
    (T : (normalizedTracePowerPositiveHalfReadoutMassEndpointPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  let L := R.toLinearHalfReadoutFamily Q C n
  exact
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_vacuumCompatibility_quadraticCylinder
      hInvariant U n k c
      M.halfExtent_gt_one M.beta_pos M.coefficient_ne_zero M.vacuum_orthogonal
      L.observable
      (fun j A =>
        (Q.normalizedTracePower_quadraticCylinder_of_linearHalfReadout
          n j (L.observable j) (L.readout j)).1 A)
      (fun j A =>
        (Q.normalizedTracePower_quadraticCylinder_of_linearHalfReadout
          n j (L.observable j) (L.readout j)).2 A)
      T hSelf

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
