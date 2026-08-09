import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryOptimalMassToPhysical
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance boundaryNoLowModeSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryNoLowModeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryNoLowModeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryNoLowModeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryNoLowModeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryNoLowModeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Failure of the literal compact-Haar Wilson boundary Poincare inequality at
one lattice scale.  The inequality is reversed strictly, so a frequently
occurring violation is the exact finite precursor of a spurious low mode. -/
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

/-- For a nonnegative candidate mass, failure of eventual boundary
admissibility produces arbitrarily fine-scale strict Poincare violations.
This is pure filter/order logic and contains no compactness assumption. -/
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

/-- The remaining reverse compactness/liminf principle in its mathematically
correct form.

If strict literal-boundary Poincare violations at a nonnegative mass occur
arbitrarily far down the lattice sequence, compactness and lower
semicontinuity must produce a genuine nonzero continuum vacuum-orthogonal
state whose graph-closed Hamiltonian Rayleigh quotient is strictly below that
mass.  This rules out finite spurious low modes disappearing in the continuum.

The structure deliberately does not assume boundary admissibility itself. -/
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
        inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) <
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

/-- The graph-closed physical Hamiltonian nonnegativity implies nonnegativity of
the variational physical Yang--Mills mass once the excitation domain is
nonempty. -/
theorem physicalYangMillsMass_nonneg_of_excitationDomainWitness
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss
      S D halfExtent N hN beta hbeta Q E R hInvariant P T)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 ≤ T.physicalYangMillsMass := by
  have hzero : (0 : ℝ) ∈ T.physicalYangMillsRayleighLowerBoundSet := by
    intro psi _hpsiNonzero _horthogonal
    simpa using T.closedRightHamiltonian_inner_nonneg psi
  exact T.rayleighLowerBound_le_physicalYangMillsMass W hzero

/-- No-low-mode-loss forces the actual variational physical mass itself to be
admissible for the literal finite Wilson boundary Poincare problem.

The proof is by contradiction: non-admissibility yields arbitrarily fine
finite violations, compactness produces a continuum Rayleigh quotient strictly
below `physicalYangMillsMass`, contradicting the theorem that the physical mass
is itself a Rayleigh lower bound. -/
theorem physicalYangMillsMass_boundaryPoincareAdmissible
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss
      S D halfExtent N hN beta hbeta Q E R hInvariant P T)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant
      T.physicalYangMillsMass := by
  have hm_nonneg := C.physicalYangMillsMass_nonneg_of_excitationDomainWitness W
  by_contra hnot
  have hfreq :=
    frequently_boundaryPoincareViolation_of_not_admissible
      (S := S) (D := D) (halfExtent := halfExtent) (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta) (Q := Q) (E := E) (R := R)
      (hInvariant := hInvariant) hm_nonneg hnot
  obtain ⟨psi, hpsiNonzero, hpsiOrthogonal, hlow⟩ :=
    C.lowMode_of_frequently_boundary_violation
      T.physicalYangMillsMass hm_nonneg hfreq
  have hRayleigh :=
    T.physicalYangMillsMass_mem_rayleighLowerBoundSet
      psi hpsiNonzero hpsiOrthogonal
  exact (not_lt_of_ge hRayleigh) hlow

/-- Combining the already-proved forward common-carrier transfer with the
reverse compactness/no-low-mode-loss principle identifies the two intrinsic
masses exactly. -/
theorem boundaryPoincareOptimalMass_eq_physicalYangMillsMass
    {B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss
      S D halfExtent N hN beta hbeta Q E R hInvariant P T)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant =
      T.physicalYangMillsMass := by
  exact
    G.boundaryPoincareOptimalMass_eq_physicalYangMillsMass_of_physical_admissible
      hP W (C.physicalYangMillsMass_boundaryPoincareAdmissible W)

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareNoLowModeLoss

end MathlibAnalytic
end MGAP4D

end