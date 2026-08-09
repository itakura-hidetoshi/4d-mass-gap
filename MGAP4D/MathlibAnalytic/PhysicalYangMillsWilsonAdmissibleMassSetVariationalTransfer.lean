import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareDirectGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryPoincareOptimalMass
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance wilsonAdmissibleTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance wilsonAdmissibleTransferSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonAdmissibleTransferSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonAdmissibleTransferSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonAdmissibleTransferSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonAdmissibleTransferSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Construct the defect-free direct-gap package from an arbitrary *positive*
element of the intrinsic literal Wilson boundary Poincare admissible-mass set.

The mass is not selected by this constructor: membership in the model-derived
set supplies exactly the eventual literal boundary inequality required by the
direct finite Wilson route. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSDirectGapOfAdmissibleMass
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
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (m : ℝ)
    (hmPos : 0 < m)
    (hm : m ∈
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := B
  mass := m
  mass_pos := hmPos
  eventually_boundary_poincare := hm.2

/-- Mass-independent common-carrier convergence for the actual finite Wilson
excitation dynamics.

Crucially, the approximation maps and evolved-norm convergence depend only on
the finite one-step Wilson operator and the continuum semigroup, not on a
chosen candidate mass.  One such bridge can therefore transport *every*
admissible literal-boundary mass. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer
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
    (B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
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
              B.physicalExcitationOneStepOperator n phi)^[
                physicalTemporalFloorNatStep S.latticeSpacing t n]
              (approximateExcitation n psi)‖)
        atTop
        (nhds ‖T.toPhysicalSemigroup.operator t (psi : P.PhysicalHilbert)‖)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer

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
    {B : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- Specialize the mass-free common-carrier bridge to any positive admissible
Wilson mass. -/
noncomputable def toDirectCommonCarrierGapTransfer
    (G : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (m : ℝ)
    (hmPos : 0 < m)
    (hm : m ∈
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant
        (physicalYangMillsEvenPeriodicWilsonOSDirectGapOfAdmissibleMass B m hmPos hm)
        P T where
  approximateExcitation := G.approximateExcitation
  approximate_norm_tendsto := G.approximate_norm_tendsto
  evolved_norm_tendsto := by
    intro t psi
    simpa [physicalYangMillsEvenPeriodicWilsonOSDirectGapOfAdmissibleMass] using
      G.evolved_norm_tendsto t psi

/-- Every intrinsic literal-Wilson admissible mass is an actual graph-closed
Hamiltonian Rayleigh lower bound.

The zero endpoint follows from nonnegativity of the physical Hamiltonian.  A
strictly positive admissible mass is transported by the direct genuine
floor-time Wilson route. -/
theorem admissibleMass_mem_physicalYangMillsRayleighLowerBoundSet
    (G : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    {m : ℝ}
    (hm : m ∈
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant) :
    m ∈ T.physicalYangMillsRayleighLowerBoundSet := by
  by_cases hzero : m = 0
  · subst m
    intro psi _hpsiNonzero _horthogonal
    simpa using T.closedRightHamiltonian_inner_nonneg psi
  · have hmPos : 0 < m := lt_of_le_of_ne hm.1 (Ne.symm hzero)
    exact
      (G.toDirectCommonCarrierGapTransfer m hmPos hm)
        |>.mass_mem_physicalYangMillsRayleighLowerBoundSet hP

/-- Set-level form: the entire model-derived Wilson admissible-mass set embeds
into the intrinsic physical-Hamiltonian Rayleigh lower-bound set. -/
theorem boundaryPoincareAdmissibleMassSet_subset_rayleighLowerBoundSet
    (G : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant ⊆
      T.physicalYangMillsRayleighLowerBoundSet := by
  intro m hm
  exact G.admissibleMass_mem_physicalYangMillsRayleighLowerBoundSet hP hm

/-- The actual variational physical mass is an upper bound for every literal
Wilson admissible mass once the continuum excitation domain is genuinely
nonempty. -/
theorem boundaryPoincareAdmissibleMassSet_bddAbove
    (G : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    BddAbove
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant) := by
  refine ⟨T.physicalYangMillsMass, ?_⟩
  intro m hm
  exact T.rayleighLowerBound_le_physicalYangMillsMass W
    (G.admissibleMass_mem_physicalYangMillsRayleighLowerBoundSet hP hm)

/-- Therefore the intrinsic optimal Wilson boundary Poincare mass is bounded
above by the actual variational physical Yang--Mills mass.

This theorem contains no selected certificate mass: it compares two intrinsic
optima, finite-Wilson boundary coercivity and continuum Hamiltonian Rayleigh
coercivity. -/
theorem boundaryPoincareOptimalMass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant ≤
      T.physicalYangMillsMass := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
  exact csSup_le hNonempty fun m hm =>
    T.rayleighLowerBound_le_physicalYangMillsMass W
      (G.admissibleMass_mem_physicalYangMillsRayleighLowerBoundSet hP hm)

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareMassFreeCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end