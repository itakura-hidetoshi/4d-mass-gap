import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonPoincareIntrinsicRateSandwich
import MGAP4D.MathlibAnalytic.PhysicalYangMillsR4ComponentRayleighExtrema
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance wilsonR4IdentitySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance wilsonR4IdentitySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonR4IdentitySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonR4IdentitySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonR4IdentitySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonR4IdentitySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {A : T.PhysicalYangMillsR4NormalizedFormDecomposition}

/-- If an actual excitation attains the direct R4 component-Rayleigh-extrema
budget, that budget is exactly the normalized variational physical mass.

This theorem contains no numerical component values. -/
theorem normalized_physicalYangMillsMass_eq_rayleighExtremaBudget_of_attained
    (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * T.physicalYangMillsMass = A.rayleighExtremaBudget := by
  have hbudget := K.canonicalBudget_eq_rayleighExtremaBudget W
  have hattainCanonical :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        (K.toCanonicalOptimalComponentData W).budget *
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    rw [hbudget]
    exact hattain
  calc
    A.referenceTime * T.physicalYangMillsMass =
        (K.toCanonicalOptimalComponentData W).budget :=
      (K.toCanonicalOptimalComponentData W).normalized_physicalYangMillsMass_eq_budget_of_attained
        psi hpsi horthogonal hattainCanonical
    _ = A.rayleighExtremaBudget := hbudget

/-- The intrinsic continuum rate reconstructed from actual finite Wilson
excitation-operator norms cannot exceed an attained R4 variational budget after
multiplication by the same positive physical reference time.

This is the one-sided, recovery-free connection between the two independently
constructed routes. -/
theorem referenceTime_mul_intrinsicRate_le_rayleighExtremaBudget_of_attained
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hlimit_pos : 0 < C.limit)
    (hP : P.IsNormalized)
    (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * C.limit ≤ A.rayleighExtremaBudget := by
  have hlimit : C.limit ≤ T.physicalYangMillsMass :=
    G.limit_le_physicalYangMillsMass hlimit_pos hP W
  have hmul := mul_le_mul_of_nonneg_left hlimit A.referenceTime_pos.le
  have hmass :=
    normalized_physicalYangMillsMass_eq_rayleighExtremaBudget_of_attained
      K W psi hpsi horthogonal hattain
  rw [hmass] at hmul
  exact hmul

/-- Once genuine reverse Wilson spectral recovery identifies the intrinsic
boundary-Poincare optimum with the physical variational mass, the independently
reconstructed finite-Wilson logarithmic rate and the attained R4 Rayleigh
budget become the same normalized quantity.

No numerical value is used in this identity. -/
theorem referenceTime_mul_intrinsicRate_eq_rayleighExtremaBudget_of_boundaryRecovery
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (hOptimalEq :
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
          S D halfExtent N hN beta hbeta Q E R hInvariant =
        T.physicalYangMillsMass)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2) :
    A.referenceTime * C.limit = A.rayleighExtremaBudget := by
  have hlimitEq : C.limit = T.physicalYangMillsMass :=
    G.limit_eq_physicalYangMillsMass_of_boundaryOptimal_eq
      hP W m hm_pos hm hOptimalEq
  have hmass :=
    normalized_physicalYangMillsMass_eq_rayleighExtremaBudget_of_attained
      K W psi hpsi horthogonal hattain
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by
      rw [hlimitEq]
    _ = A.rayleighExtremaBudget := hmass

/-- Fully linked exact-value endpoint.

The number `33/20` is emitted only after all of the following independent
Yang--Mills obligations are supplied:

* the intrinsic finite Wilson rate sequence and common-carrier continuum
  transfer;
* genuine reverse Wilson spectral recovery;
* an actual R4 component decomposition and boundedness package;
* a genuine state attaining the direct component-Rayleigh-extrema budget;
* exact evaluation of those six actual variational extrema.

Neither the Wilson rate nor the physical mass is set equal to the target value
in any input. -/
theorem referenceTime_mul_intrinsicRate_eq_33_over_20_of_complete_linked_data
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (K : T.PhysicalYangMillsR4ComponentBoundednessData A)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (hOptimalEq :
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
          S D halfExtent N hN beta hbeta Q E R hInvariant =
        T.physicalYangMillsMass)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0)
    (hattain :
      A.referenceTime *
          inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) =
        A.rayleighExtremaBudget * ‖(psi : P.PhysicalHilbert)‖ ^ 2)
    (hbase :
      sInf (T.physicalYangMillsComponentRayleighSet A.qBase) = (9 : ℝ) / 5)
    (hcurv :
      sInf (T.physicalYangMillsComponentRayleighSet A.qCurvature) = (1 : ℝ) / 10)
    (hintpos :
      sInf (T.physicalYangMillsComponentRayleighSet A.qInteractionPositive) = 0)
    (hleak :
      sSup (T.physicalYangMillsComponentRayleighSet A.qInteractionLeak) = (1 : ℝ) / 10)
    (hboundary :
      sSup (T.physicalYangMillsComponentRayleighSet A.qBoundaryError) = (1 : ℝ) / 20)
    (hreg :
      sSup (T.physicalYangMillsComponentRayleighSet A.qRegularizationError) = (1 : ℝ) / 10) :
    A.referenceTime * C.limit = (33 : ℝ) / 20 := by
  have hlimitEq : C.limit = T.physicalYangMillsMass :=
    G.limit_eq_physicalYangMillsMass_of_boundaryOptimal_eq
      hP W m hm_pos hm hOptimalEq
  calc
    A.referenceTime * C.limit = A.referenceTime * T.physicalYangMillsMass := by
      rw [hlimitEq]
    _ = (33 : ℝ) / 20 :=
      K.normalized_physicalYangMillsMass_eq_33_over_20_of_component_rayleigh_extrema_and_attainment
        W psi hpsi horthogonal hattain hbase hcurv hintpos hleak hboundary hreg

end PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end