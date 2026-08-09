import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalExcitationDirichletLowerBoundGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExponentialGapSlope
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOptimalRayleighCoercivity
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance floorExcitationCommonCarrierSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance floorExcitationCommonCarrierSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance floorExcitationCommonCarrierSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance floorExcitationCommonCarrierSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance floorExcitationCommonCarrierSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance floorExcitationCommonCarrierSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Scalar-norm common-carrier transfer for the corrected **genuine integer
floor-time** finite Wilson excitation evolution.

Unlike the legacy `ApproximatingVacuumGapCertificate` route, this structure has
no all-real finite-volume semigroup, no freely supplied finite decay factor,
and no independently supplied finite mass.  The finite dynamics are fixed to
the actual completed one-step physical excitation operators from the Wilson OS
construction and their floor-selected iterates.

Only the cross-scale comparison remains model-dependent:

* approximate a continuum vacuum-orthogonal state by a finite
  vacuum-orthogonal excitation state;
* preserve its norm in the limit;
* require the norm of the actual floor-evolved finite state to converge to the
  norm of the continuum OS semigroup state.

This is enough because the finite lower-bound certificate already proves the
uniform floor-time exponential estimate. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer
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
    (A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup) where
  approximateExcitation :
    (n : ℕ) → P.VacuumOrthogonalHilbert →L[ℝ]
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert
  approximate_norm_tendsto :
    ∀ psi : P.VacuumOrthogonalHilbert,
      Tendsto (fun n => ‖approximateExcitation n psi‖)
        atTop (nhds ‖psi‖)
  evolved_norm_tendsto :
    ∀ (t : NNReal) (psi : P.VacuumOrthogonalHilbert),
      Tendsto
        (fun n =>
          ‖(fun phi :
              (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
                S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert =>
              A.boundedAnalysis.physicalExcitationOneStepOperator n phi)^[
                physicalTemporalFloorNatStep S.latticeSpacing t n]
              (approximateExcitation n psi)‖)
        atTop
        (nhds ‖T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert)‖)

namespace PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer

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
    {A : PhysicalYangMillsEvenPeriodicWilsonOSPhysicalExcitationDirichletLowerBoundCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- The genuine finite floor-time Wilson decay passes directly to the continuum
vacuum-orthogonal OS semigroup by scalar norm convergence. -/
theorem continuumExcitation_norm_le_exp
    (G : PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (t : NNReal)
    (psi : P.VacuumOrthogonalHilbert) :
    ‖T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert)‖ ≤
      Real.exp (-A.mass * (t : ℝ)) * ‖psi‖ := by
  exact
    A.floorPhysicalExcitationIterate_limit_norm_le
      t
      (fun n => G.approximateExcitation n psi)
      (G.approximate_norm_tendsto psi)
      (G.evolved_norm_tendsto t psi)

/-- The corrected floor-time transfer therefore constructs the continuum
vacuum-semigroup gap slope with the concrete exponential decay factor.  No
legacy finite all-real semigroup certificate occurs. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T) :
    T.VacuumSemigroupGapSlope where
  mass := A.mass
  mass_pos := A.mass_pos
  decayFactor := fun t => Real.exp (-A.mass * (t : ℝ))
  slope_tendsto :=
    tendsto_nnreal_inv_mul_one_sub_exp_neg_mul A.mass
  decay := by
    intro t psi hpsi
    have hmem : psi ∈ P.vacuumOrthogonal := by
      rw [P.mem_vacuumOrthogonal_iff, real_inner_comm]
      exact hpsi
    let psiOrth : P.VacuumOrthogonalHilbert := ⟨psi, hmem⟩
    have h := G.continuumExcitation_norm_le_exp t psiOrth
    simpa [psiOrth] using h

/-- Hence the actual graph-closed OS Hamiltonian has Rayleigh quotient at least
the mass generated by the finite Wilson Dirichlet lower-bound route. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    A.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) :=
  PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.StronglyContinuousPhysicalSemigroup.VacuumSemigroupGapSlope.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    T G.toVacuumSemigroupGapSlope hP psi hpsi

/-- The corrected floor-time Wilson mass lower bound is therefore an admissible
coercivity constant for the actual variational physical Yang--Mills
Hamiltonian. -/
theorem mass_mem_physicalYangMillsRayleighLowerBoundSet
    (G : PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (hP : P.IsNormalized) :
    A.mass ∈ T.physicalYangMillsRayleighLowerBoundSet := by
  intro psi _hpsiNonzero horthogonal
  exact G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    hP psi horthogonal

/-- Consequently every mass lower bound proved through the genuine finite
Wilson floor-time route lies below the intrinsic variational physical
Yang--Mills mass, provided the actual excitation domain is nonempty. -/
theorem mass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    A.mass ≤ T.physicalYangMillsMass :=
  T.rayleighLowerBound_le_physicalYangMillsMass
    W (G.mass_mem_physicalYangMillsRayleighLowerBoundSet hP)

/-- If a complete Wilson analysis later proves that the corrected floor-time
mass lower bound is the greatest admissible Rayleigh coercivity constant, the
actual physical Yang--Mills mass is theorem-generated as that value.  Equality
is not stored as a certificate field. -/
theorem physicalYangMillsMass_eq_of_isGreatest
    (G : PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant A P T)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (hGreatest : IsGreatest T.physicalYangMillsRayleighLowerBoundSet A.mass) :
    T.physicalYangMillsMass = A.mass :=
  T.physicalYangMillsMass_eq_of_isGreatest_rayleighLowerBoundSet
    W hGreatest

end PhysicalYangMillsEvenPeriodicWilsonOSFloorExcitationCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end