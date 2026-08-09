import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundarySharpRecovery
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance boundaryNoLowModeV2SideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryNoLowModeV2SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryNoLowModeV2SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryNoLowModeV2SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryNoLowModeV2SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryNoLowModeV2SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- A strict failure of the literal compact-Haar Wilson boundary Poincare
inequality at one finite scale. -/
def physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareViolationAtScale
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (m : ℝ) (n : ℕ) : Prop :=
  ∃ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
        S D halfExtent N hN beta hbeta Q E R hInvariant n F <
      (2 * m * S.latticeSpacing n) *
        (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N))

/-- For a nonnegative candidate mass, non-admissibility means that strict
finite-scale violations occur arbitrarily far down the lattice sequence. -/
theorem frequently_boundaryPoincareViolation_of_not_admissible
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
    {m : ℝ}
    (hm_nonneg : 0 ≤ m)
    (hnot : ¬ physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    ∃ᶠ n in atTop,
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareViolationAtScale
        S D halfExtent N hN beta hbeta Q E R hInvariant m n := by
  have hnotEventually :
      ¬ ∀ᶠ n in atTop,
        ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
        let Pn :=
          physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
        let Fc := Pn.vacuumCenteredCarrier F
        (2 * m * S.latticeSpacing n) *
            (∫ b,
              ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
                S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
              ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
          physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
            S D halfExtent N hN beta hbeta Q E R hInvariant n F := by
    intro hEventually
    exact hnot ⟨hm_nonneg, hEventually⟩
  simpa only [Filter.Frequently,
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareViolationAtScale,
    not_exists, not_lt, not_forall, not_le] using hnotEventually

/-- Correct compactness/liminf form of the no-low-mode-loss principle.

If strict finite Wilson boundary Poincare violations at a nonnegative level
`m` occur arbitrarily far down the lattice sequence, compactness and lower
semicontinuity produce a genuine nonzero continuum vacuum-orthogonal state
whose graph-closed Hamiltonian Rayleigh energy is **at most** `m`.

The non-strict conclusion is essential: violation margins may shrink to zero.
Consequently this principle recovers every strict lower approximation
`m < physicalYangMillsMass`, without incorrectly asserting endpoint
attainment. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup) where
  lowMode_of_frequently_boundary_violation :
    ∀ m : ℝ, 0 ≤ m →
      (∃ᶠ n in atTop,
        physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareViolationAtScale
          S D halfExtent N hN beta hbeta Q E R hInvariant m n) →
      ∃ psi : T.closedRightHamiltonian.domain,
        (psi : P.PhysicalHilbert) ≠ 0 ∧
        inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 ∧
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) ≤
          m * ‖(psi : P.PhysicalHilbert)‖ ^ 2

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss

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
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- No-low-mode-loss theorem-generates every nonnegative strict lower
approximation to the continuum physical mass as an admissible literal Wilson
boundary Poincare mass. -/
theorem strict_lower_mass_admissible
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss
      S D halfExtent N hN beta hbeta Q E R hInvariant P T)
    (m : ℝ)
    (hm_nonneg : 0 ≤ m)
    (hm_lt : m < T.physicalYangMillsMass) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m := by
  by_contra hnot
  have hfreq :=
    frequently_boundaryPoincareViolation_of_not_admissible
      (S := S) (D := D) (halfExtent := halfExtent) (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta) (Q := Q) (E := E) (R := R)
      (hInvariant := hInvariant) hm_nonneg hnot
  obtain ⟨psi, hpsiNonzero, hpsiOrthogonal, hlow⟩ :=
    C.lowMode_of_frequently_boundary_violation m hm_nonneg hfreq
  have hRayleigh :=
    T.physicalYangMillsMass_mem_rayleighLowerBoundSet
      psi hpsiNonzero hpsiOrthogonal
  have hnorm_sq_pos : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hpsiNonzero)
  nlinarith

/-- Package compactness/no-low-mode-loss as the already-proved sharp recovery
interface.  Nonemptiness remains a separate finite-Wilson fact; endpoint
admissibility is not required. -/
noncomputable def toSharpRecoveryData
    {B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss
      S D halfExtent N hN beta hbeta Q E R hInvariant P T)
    (hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty) :
    PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareSharpRecoveryData
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T G where
  admissible_nonempty := hNonempty
  all_strict_lower_admissible := by
    intro m hm_nonneg hm_lt
    exact C.strict_lower_mass_admissible m hm_nonneg hm_lt

/-- Forward common-carrier transfer plus reverse no-low-mode-loss compactness
identifies the intrinsic literal-Wilson boundary optimum with the actual
continuum variational Yang--Mills mass. -/
theorem boundaryPoincareOptimalMass_eq_physicalYangMillsMass
    {B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss
      S D halfExtent N hN beta hbeta Q E R hInvariant P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant =
      T.physicalYangMillsMass :=
  (C.toSharpRecoveryData (G := G) hNonempty).boundaryPoincareOptimalMass_eq_physicalYangMillsMass
    hP W

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss

end MathlibAnalytic
end MGAP4D

end