import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerPositiveHalfReadoutMassEndpoint
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedTracePowerFinitePositiveHalfObservableBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Topology
open scoped ENNReal InnerProduct InnerProductSpace

noncomputable section

private theorem normalizedTracePowerSupportPositiveHalfReadoutMassEndpointTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance normalizedTracePowerSupportPositiveHalfReadoutMassEndpointNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance normalizedTracePowerSupportPositiveHalfReadoutMassEndpointTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance normalizedTracePowerSupportPositiveHalfReadoutMassEndpointCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance normalizedTracePowerSupportPositiveHalfReadoutMassEndpointSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance normalizedTracePowerSupportPositiveHalfReadoutMassEndpointMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance normalizedTracePowerSupportPositiveHalfReadoutMassEndpointBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance normalizedTracePowerSupportPositiveHalfReadoutMassEndpointSU2Nontrivial :
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

private abbrev normalizedTracePowerSupportPositiveHalfReadoutMassEndpointPreHilbert
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfReadoutMassEndpointTwoRankPositive
        beta hbeta)
    (hInvariant : ∀ m,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S m))
    (n : ℕ) :=
  physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
    S D halfExtent 2
      normalizedTracePowerSupportPositiveHalfReadoutMassEndpointTwoRankPositive
      beta hbeta Q.toWeakStarBridge hInvariant n

/-- For one normalized-trace polynomial, pointwise positive-half cylinder
realization is needed only on the nonzero coefficient support.

Each supported linear readout is reflected theoremically, polarized to the
quadratic identities, and converted by vacuum compatibility into an exact
positive-half pullback preimage.  The already-proved equality between the
finite OS observable image and the coherent pullback range then supplies the
supportwise finite-range hypotheses consumed by the reconstructed Hamiltonian
endpoint.

Thus this theorem removes the stronger countable-family readout premise: no
observable is requested for a trace power whose polynomial coefficient is
zero.  No density, whole-algebra lift, global surjectivity, multiplicativity,
or new Hamiltonian hypothesis is introduced. -/
theorem
    normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_vacuumCompatibility_support_positiveHalfReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2
        normalizedTracePowerSupportPositiveHalfReadoutMassEndpointTwoRankPositive
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
    (F : Fin (k + 1) → D.positiveTimeSubalgebra)
    (R : ∀ j : Fin (k + 1), c j ≠ 0 →
      NormalizedTracePowerPositiveHalfReadout Q n (j : ℕ) (F j))
    (T : (normalizedTracePowerSupportPositiveHalfReadoutMassEndpointPreHilbert
      Q hInvariant n).StronglyContinuousPhysicalSemigroup)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    0 ≤ T.physicalYangMillsMass := by
  apply
    Q.normalizedTracePolynomial_physicalYangMillsMass_nonneg_of_support_rawPowerBounded_mem_finitePositiveHalfObservableRange
      hInvariant U n k c
      M.halfExtent_gt_one M.beta_pos M.coefficient_ne_zero M.vacuum_orthogonal
      _ T hSelf
  intro j hcj
  rw [Q.finitePositiveHalfObservable_range_eq_positiveHalfPullback_range hInvariant n]
  let L := (R j hcj).toLinearHalfReadout Q C n (j : ℕ) (F j)
  refine ⟨⟨(F j).1, (F j).2⟩, ?_⟩
  exact
    Q.normalizedTracePower_positiveHalfPullback_eq_of_vacuumCompatibility_linearHalfReadout
      hInvariant U n (j : ℕ) (F j) L

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
