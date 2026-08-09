import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryPoincareOptimalMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareDirectGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianNonnegative
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance boundaryOptimalPhysicalSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryOptimalPhysicalSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryOptimalPhysicalSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryOptimalPhysicalSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryOptimalPhysicalSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryOptimalPhysicalSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Cross-scale carrier data independent of any selected mass.

The actual finite dynamics are fixed once and for all by the completed Wilson
physical-excitation one-step operators.  A mass enters only later through a
literal boundary Poincare inequality.  Consequently the same approximation
maps and evolved-norm convergence can transport *every* admissible boundary
mass to the continuum OS semigroup. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
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
      Tendsto (fun n => ‖approximateExcitation n psi‖) atTop (nhds ‖psi‖)
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer

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

/-- Every strictly positive intrinsic boundary-admissible mass canonically
constructs the defect-free direct gap certificate. -/
noncomputable def toDirectGapCertificateOfAdmissible
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := B
  mass := m
  mass_pos := hm_pos
  eventually_boundary_poincare := hm.2

/-- The mass-free carrier transfer specializes to the direct common-carrier gap
transfer at every positive admissible mass. -/
noncomputable def toDirectCommonCarrierGapTransferOfAdmissible
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant
        (G.toDirectGapCertificateOfAdmissible m hm_pos hm) P T where
  approximateExcitation := G.approximateExcitation
  approximate_norm_tendsto := G.approximate_norm_tendsto
  evolved_norm_tendsto := G.evolved_norm_tendsto

/-- Every positive mass selected by the literal compact-Haar Wilson boundary
Poincare form lies below the intrinsic variational physical Yang--Mills mass. -/
theorem positive_admissibleMass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (m : ℝ)
    (hm_pos : 0 < m)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    m ≤ T.physicalYangMillsMass := by
  have h :=
    (G.toDirectCommonCarrierGapTransferOfAdmissible m hm_pos hm).mass_le_physicalYangMillsMass
      hP W
  simpa [toDirectGapCertificateOfAdmissible] using h

/-- Nonnegativity of the graph-closed physical Hamiltonian makes zero a valid
actual Rayleigh lower bound, hence the variational physical mass is nonnegative
whenever the physical excitation domain is nonempty. -/
theorem physicalYangMillsMass_nonneg
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 ≤ T.physicalYangMillsMass := by
  have hzero : (0 : ℝ) ∈ T.physicalYangMillsRayleighLowerBoundSet := by
    intro psi _hpsiNonzero _horthogonal
    simpa using T.closedRightHamiltonian_inner_nonneg psi
  exact T.rayleighLowerBound_le_physicalYangMillsMass W hzero

/-- Therefore *every* intrinsic boundary-admissible mass, including the endpoint
zero, is bounded above by the physical Yang--Mills mass. -/
theorem admissibleMass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (m : ℝ)
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    m ≤ T.physicalYangMillsMass := by
  rcases hm with ⟨hm_nonneg, hmPoincare⟩
  rcases lt_or_eq_of_le hm_nonneg with hm_pos | hm_zero
  · exact G.positive_admissibleMass_le_physicalYangMillsMass
      hP W m hm_pos ⟨hm_nonneg, hmPoincare⟩
  · rw [← hm_zero]
    exact G.physicalYangMillsMass_nonneg W

/-- The intrinsic optimal literal-Wilson boundary Poincare mass is bounded by
the actual variational physical Yang--Mills mass.  No certificate-selected mass
appears in the statement. -/
theorem boundaryPoincareOptimalMass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
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
    G.admissibleMass_le_physicalYangMillsMass hP W m hm

/-- If the physical variational mass itself is admissible for the literal
Wilson boundary Poincare problem, then the two intrinsic masses coincide.

This theorem isolates the remaining hard reverse direction cleanly: proving
that the continuum variational optimum is attained/approximated by the actual
finite Wilson boundary coercivity problem. -/
theorem boundaryPoincareOptimalMass_eq_physicalYangMillsMass_of_physical_admissible
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (hPhysical :
      T.physicalYangMillsMass ∈
        physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
          S D halfExtent N hN beta hbeta Q E R hInvariant) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant =
      T.physicalYangMillsMass := by
  have hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty :=
    ⟨T.physicalYangMillsMass, hPhysical⟩
  have hupper :=
    G.boundaryPoincareOptimalMass_le_physicalYangMillsMass hP W hNonempty
  have hBounded :
      BddAbove
        (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
          S D halfExtent N hN beta hbeta Q E R hInvariant) := by
    refine ⟨T.physicalYangMillsMass, ?_⟩
    intro m hm
    exact G.admissibleMass_le_physicalYangMillsMass hP W m hm
  have hlower :
      T.physicalYangMillsMass ≤
        physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
          S D halfExtent N hN beta hbeta Q E R hInvariant := by
    unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
    exact le_csSup hBounded hPhysical
  exact le_antisymm hupper hlower

end PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end