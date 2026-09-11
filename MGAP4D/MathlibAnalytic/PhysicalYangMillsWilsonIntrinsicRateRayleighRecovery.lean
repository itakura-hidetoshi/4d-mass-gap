import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonRateR4RayleighBudgetIdentity
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance rayleighRecoverySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance rayleighRecoverySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance rayleighRecoverySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance rayleighRecoverySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance rayleighRecoverySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance rayleighRecoverySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Variational recovery of the intrinsic finite Wilson logarithmic rate by
actual nonzero vacuum-orthogonal states of the graph-closed continuum
Hamiltonian.

The data do **not** contain an equality between a Wilson optimum and the
physical mass.  Instead they require a genuine recovery sequence `psi_n` whose
actual continuum Rayleigh quotients differ from the finite Wilson rates

`g_n = -log ||T_n^exc|| / a_n`

by a quantity tending to zero.  Constructing such states from finite slow modes
is the model-specific compactness / Mosco-recovery obligation. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery
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
  rayleighRateError_tendsto_zero :
    Tendsto
      (fun n =>
        T.physicalYangMillsClosedRayleighQuotient (recoveryState n) -
          physicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredMassRate
            C.boundedAnalysis n)
      atTop (nhds 0)

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery

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

/-- A recovery sequence asymptotic to the finite Wilson rates has actual
continuum Hamiltonian Rayleigh quotients converging to the intrinsic Wilson
rate limit. -/
theorem rayleighQuotient_tendsto_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T) :
    Tendsto
      (fun n => T.physicalYangMillsClosedRayleighQuotient (V.recoveryState n))
      atTop (nhds C.limit) := by
  have hsum := V.rayleighRateError_tendsto_zero.add C.rate_tendsto_limit
  simpa only [sub_add_cancel, zero_add] using hsum

/-- Variational recovery gives the reverse inequality

`physicalYangMillsMass <= C.limit`.

This uses only that the physical mass is the infimum of actual excitation
Rayleigh values and that the recovery-state Rayleigh values converge to the
intrinsic Wilson rate. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T) :
    T.physicalYangMillsMass ≤ C.limit := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds V.rayleighQuotient_tendsto_limit
  exact Filter.Eventually.of_forall fun n =>
    T.physicalYangMillsMass_le_rayleigh
      ⟨V.recoveryState n, V.recoveryState_ne_zero n,
        V.recoveryState_orthogonal n, rfl⟩

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

/-- A concrete Rayleigh recovery sequence replaces the previous abstract
endpoint equality.  A single positive Wilson-admissible mass gives positivity
of `C.limit`; the already integrated common-carrier theorem gives
`C.limit <= m_YM`; recovery gives the reverse inequality. -/
theorem limit_eq_physicalYangMillsMass_of_rayleighRecovery
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (W : T.PhysicalYangMillsExcitationDomainWitness)
    (m : ℝ) (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T) :
    C.limit = T.physicalYangMillsMass := by
  have hlimit_pos : 0 < C.limit := C.limit_pos_of_positive_admissibleMass m hm_pos hm
  exact le_antisymm
    (G.limit_le_physicalYangMillsMass hlimit_pos hP W)
    V.physicalYangMillsMass_le_limit

/-- With Rayleigh recovery, the Wilson logarithmic rate and an attained R4
component-Rayleigh-extrema budget are the same normalized quantity without
assuming `boundaryPoincareOptimalMass = physicalYangMillsMass`. -/
theorem referenceTime_mul_intrinsicRate_eq_rayleighExtremaBudget_of_rayleighRecovery
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness) (m : ℝ) (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T)
    (psi : T.closedRightHamiltonian.domain) (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain : A.referenceTime * inner ℝ (T.closedRightHamiltonian psi)
      (psi : P.PhysicalHilbert) = A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * C.limit = A.rayleighExtremaBudget := by
  have hlimitEq := G.limit_eq_physicalYangMillsMass_of_rayleighRecovery
    hP W m hm_pos hm V
  have hmass := normalized_physicalYangMillsMass_eq_rayleighExtremaBudget_of_attained
    K W psi hpsi horthogonal hattain
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by rw [hlimitEq]
    _ = A.rayleighExtremaBudget := hmass

/-- Exact linked endpoint with the abstract Wilson/physical optimum equality
removed.  The hard reverse obligation is now the actual asymptotic recovery
condition `R_H(psi_n) - g_n -> 0`.

The final `33/20` still requires independent evaluation of the six actual R4
component Rayleigh extrema and an attained R4 budget. -/
theorem referenceTime_mul_intrinsicRate_eq_33_over_20_of_rayleighRecovery
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness) (m : ℝ) (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T)
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
  have hlimitEq := G.limit_eq_physicalYangMillsMass_of_rayleighRecovery
    hP W m hm_pos hm V
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by rw [hlimitEq]
    _ = (33 : ℝ) / 20 :=
      K.normalized_physicalYangMillsMass_eq_33_over_20_of_component_rayleigh_extrema_and_attainment
        W psi hpsi horthogonal hattain hbase hcurv hintpos hleak hboundary hreg

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end