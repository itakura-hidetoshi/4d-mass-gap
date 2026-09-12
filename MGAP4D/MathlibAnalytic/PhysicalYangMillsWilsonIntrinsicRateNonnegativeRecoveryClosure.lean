import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonIntrinsicRateRayleighRecovery
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance nonnegativeRecoverySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance nonnegativeRecoverySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance nonnegativeRecoverySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance nonnegativeRecoverySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance nonnegativeRecoverySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance nonnegativeRecoverySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

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

/-- The intrinsic Wilson rate limit is nonnegative because every finite rate
`-log ||T_n^exc|| / a_n` is nonnegative and the sequence converges. -/
theorem limit_nonneg
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant) :
    0 ≤ C.limit := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds C.rate_tendsto_limit
  exact Filter.Eventually.of_forall fun n => C.intrinsicCenteredMassRate_nonneg n

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence

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

/-- A Rayleigh recovery sequence already contains a genuine nonzero
vacuum-orthogonal closed-Hamiltonian state, so it canonically supplies the
excitation-domain witness needed by the variational mass theorems. -/
def toExcitationDomainWitness
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T) :
    T.PhysicalYangMillsExcitationDomainWitness where
  state := V.recoveryState 0
  state_ne_zero := V.recoveryState_ne_zero 0
  state_orthogonal := V.recoveryState_orthogonal 0

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

/-- The forward Wilson-rate inequality no longer needs a separately supplied
strictly positive admissible mass.

If `C.limit = 0`, it follows from nonnegativity of the physical variational
mass.  Otherwise `C.limit > 0` follows from the intrinsic limit nonnegativity,
and the existing positive-rate semigroup theorem applies. -/
theorem limit_le_physicalYangMillsMass_without_strictPos
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (W : T.PhysicalYangMillsExcitationDomainWitness) :
    C.limit ≤ T.physicalYangMillsMass := by
  by_cases hzero : C.limit = 0
  · rw [hzero]
    exact T.physicalYangMillsMass_nonneg W
  · have hpos : 0 < C.limit :=
      lt_of_le_of_ne C.limit_nonneg (Ne.symm hzero)
    exact G.limit_le_physicalYangMillsMass hpos hP W

/-- Rayleigh recovery by itself now identifies the intrinsic Wilson rate with
the physical variational mass.  No positive mass certificate and no abstract
Wilson-optimum/physical-mass equality is an input. -/
theorem limit_eq_physicalYangMillsMass_of_rayleighRecovery_only
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T) :
    C.limit = T.physicalYangMillsMass := by
  let W := V.toExcitationDomainWitness
  exact le_antisymm
    (G.limit_le_physicalYangMillsMass_without_strictPos hP W)
    V.physicalYangMillsMass_le_limit

/-- Fully intrinsic R4 identity: once the actual Rayleigh recovery sequence and
an attained R4 variational budget are available, no auxiliary positive Wilson
mass is needed. -/
theorem referenceTime_mul_intrinsicRate_eq_rayleighExtremaBudget_of_recovery_only
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateRayleighRecovery C P T)
    (psi : T.closedRightHamiltonian.domain) (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain : A.referenceTime * inner ℝ (T.closedRightHamiltonian psi)
      (psi : P.PhysicalHilbert) = A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * C.limit = A.rayleighExtremaBudget := by
  let W := V.toExcitationDomainWitness
  have hlimitEq := G.limit_eq_physicalYangMillsMass_of_rayleighRecovery_only hP V
  have hmass := normalized_physicalYangMillsMass_eq_rayleighExtremaBudget_of_attained
    K W psi hpsi horthogonal hattain
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by rw [hlimitEq]
    _ = A.rayleighExtremaBudget := hmass

/-- Exact endpoint with both previous auxiliary reverse inputs removed.  The
remaining reverse spectral obligation is solely the recovery sequence
`R_H(psi_n) - g_n -> 0`; the final number still requires actual R4 extremum
evaluation, budget attainment, and a model-derived reference time. -/
theorem referenceTime_mul_intrinsicRate_eq_33_over_20_of_recovery_only
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized) (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
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
  let W := V.toExcitationDomainWitness
  have hlimitEq := G.limit_eq_physicalYangMillsMass_of_rayleighRecovery_only hP V
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by rw [hlimitEq]
    _ = (33 : ℝ) / 20 :=
      K.normalized_physicalYangMillsMass_eq_33_over_20_of_component_rayleigh_extrema_and_attainment
        W psi hpsi horthogonal hattain hbase hcurv hintpos hleak hboundary hreg

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end