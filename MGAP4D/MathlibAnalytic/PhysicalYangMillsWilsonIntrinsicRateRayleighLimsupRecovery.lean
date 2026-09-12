import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonIntrinsicRateNonnegativeRecoveryClosure
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance limsupRecoverySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance limsupRecoverySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance limsupRecoverySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance limsupRecoverySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance limsupRecoverySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance limsupRecoverySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- One-sided variational recovery of the intrinsic finite Wilson rates.

For the reverse inequality it is unnecessary to ask that the continuum
Rayleigh values converge *equal* to the finite rates.  It is enough to have a
vanishing excess `eps_n -> 0` and actual nonzero vacuum-orthogonal closed-domain
states satisfying

`R_H(psi_n) <= g_n + eps_n`.

This is the natural Mosco/Gamma-limsup recovery condition for the variational
mass. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (P : D.OSPreHilbertData) (T : P.StronglyContinuousPhysicalSemigroup) where
  recoveryState : ℕ → T.closedRightHamiltonian.domain
  recoveryState_ne_zero : ∀ n, (recoveryState n : P.PhysicalHilbert) ≠ 0
  recoveryState_orthogonal : ∀ n,
    inner ℝ (recoveryState n : P.PhysicalHilbert) P.vacuum = 0
  excess : ℕ → ℝ
  excess_tendsto_zero : Tendsto excess atTop (nhds 0)
  rayleigh_le_rate_add_excess : ∀ n,
    T.physicalYangMillsClosedRayleighQuotient (recoveryState n) ≤
      physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
        C.boundedAnalysis n + excess n

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData} {T : P.StronglyContinuousPhysicalSemigroup}

/-- The finite Wilson rate plus the vanishing recovery excess converges to the
same intrinsic rate limit. -/
theorem rate_add_excess_tendsto_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery C P T) :
    Tendsto
      (fun n =>
        physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
          C.boundedAnalysis n + V.excess n)
      atTop (nhds C.limit) := by
  simpa only [add_zero] using C.rate_tendsto_limit.add V.excess_tendsto_zero

/-- The one-sided recovery condition is sufficient for the reverse variational
inequality `physicalYangMillsMass <= C.limit`. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery C P T) :
    T.physicalYangMillsMass ≤ C.limit := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds V.rate_add_excess_tendsto_limit
  exact Filter.Eventually.of_forall fun n =>
    (T.physicalYangMillsMass_le_rayleigh
      ⟨V.recoveryState n, V.recoveryState_ne_zero n,
        V.recoveryState_orthogonal n, rfl⟩).trans
      (V.rayleigh_le_rate_add_excess n)

/-- A one-sided recovery sequence itself supplies a genuine excitation-domain
witness. -/
def toExcitationDomainWitness
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery C P T) :
    T.PhysicalYangMillsExcitationDomainWitness where
  state := V.recoveryState 0
  state_ne_zero := V.recoveryState_ne_zero 0
  state_orthogonal := V.recoveryState_orthogonal 0

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData} {T : P.StronglyContinuousPhysicalSemigroup}

/-- The stronger two-sided recovery package from #1560 canonically yields the
one-sided Mosco-limsup package by taking the absolute rate error as the
vanishing excess. -/
noncomputable def toLimsupRecovery
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T) :
    PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery C P T where
  recoveryState := V.recoveryState
  recoveryState_ne_zero := V.recoveryState_ne_zero
  recoveryState_orthogonal := V.recoveryState_orthogonal
  excess := fun n =>
    |T.physicalYangMillsClosedRayleighQuotient (V.recoveryState n) -
      physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
        C.boundedAnalysis n|
  excess_tendsto_zero := by
    simpa using V.rayleighRateError_tendsto_zero.abs
  rayleigh_le_rate_add_excess := by
    intro n
    have h := le_abs_self
      (T.physicalYangMillsClosedRayleighQuotient (V.recoveryState n) -
        physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
          C.boundedAnalysis n)
    linarith

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData} {T : P.StronglyContinuousPhysicalSemigroup}
    {A : T.PhysicalYangMillsR4NormalizedFormDecomposition}

/-- The minimal one-sided variational recovery condition identifies the
intrinsic finite Wilson rate limit with the physical Yang--Mills mass. -/
theorem limit_eq_physicalYangMillsMass_of_limsupRecovery
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery C P T) :
    C.limit = T.physicalYangMillsMass := by
  let W := V.toExcitationDomainWitness
  exact le_antisymm
    (G.limit_le_physicalYangMillsMass_without_strictPos hP W)
    V.physicalYangMillsMass_le_limit

/-- With only Mosco-limsup recovery and an attained R4 budget, the Wilson rate
and R4 variational budget are the same normalized quantity. -/
theorem referenceTime_mul_intrinsicRate_eq_rayleighExtremaBudget_of_limsupRecovery
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery C P T)
    (psi : T.closedRightHamiltonian.domain) (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain : A.referenceTime * inner ℝ (T.closedRightHamiltonian psi)
      (psi : P.PhysicalHilbert) = A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * C.limit = A.rayleighExtremaBudget := by
  let W := V.toExcitationDomainWitness
  have hlimitEq := G.limit_eq_physicalYangMillsMass_of_limsupRecovery hP V
  have hmass := normalized_physicalYangMillsMass_eq_rayleighExtremaBudget_of_attained
    K W psi hpsi horthogonal hattain
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by rw [hlimitEq]
    _ = A.rayleighExtremaBudget := hmass

/-- Exact endpoint with the reverse Wilson-to-continuum obligation weakened to
one-sided variational recovery.  The target rational remains only the final
arithmetic output after actual R4 extremum evaluation and budget attainment. -/
theorem referenceTime_mul_intrinsicRate_eq_33_over_20_of_limsupRecovery
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighLimsupRecovery C P T)
    (psi : T.closedRightHamiltonian.domain) (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain : A.referenceTime * inner ℝ (T.closedRightHamiltonian psi)
      (psi : P.PhysicalHilbert) = A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hbase : sInf (T.physicalYangMillsComponentRayleighSet A.qBase) = (9 : ℝ) / 5)
    (hcurv : sInf (T.physicalYangMillsComponentRayleighSet A.qCurvature) = (1 : ℝ) / 10)
    (hintpos : sInf (T.physicalYangMillsComponentRayleighSet A.qInteractionPositive) = 0)
    (hleak : sSup (T.physicalYangMillsComponentRayleighSet A.qInteractionLeak) = (1 : ℝ) / 10)
    (hboundary : sSup (T.physicalYangMillsComponentRayleighSet A.qBoundaryError) = (1 : ℝ) / 20)
    (hreg : sSup (T.physicalYangMillsComponentRayleighSet A.qRegularizationError) = (1 : ℝ) / 10) :
    A.referenceTime * C.limit = (33 : ℝ) / 20 := by
  let W := V.toExcitationDomainWitness
  have hlimitEq := G.limit_eq_physicalYangMillsMass_of_limsupRecovery hP V
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by rw [hlimitEq]
    _ = (33 : ℝ) / 20 :=
      K.normalized_physicalYangMillsMass_eq_33_over_20_of_component_rayleigh_extrema_and_attainment
        W psi hpsi horthogonal hattain hbase hcurv hintpos hleak hboundary hreg

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end