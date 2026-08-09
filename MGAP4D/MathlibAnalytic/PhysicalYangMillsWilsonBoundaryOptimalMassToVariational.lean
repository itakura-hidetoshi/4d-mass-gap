import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSLiteralBoundaryPoincareDirectGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryPoincareOptimalMass
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianNonnegative
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance wilsonOptimalToVariationalSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance wilsonOptimalToVariationalSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonOptimalToVariationalSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonOptimalToVariationalSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonOptimalToVariationalSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonOptimalToVariationalSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Mass-independent common-carrier convergence for the genuine floor-selected
finite Wilson excitation evolution.

The finite operator family is fixed by the actual bounded Wilson one-step
analysis `B`.  No distinguished mass, defect coefficient, decay factor, or
all-real finite semigroup occurs in this structure.  Once this cross-scale
convergence has been proved for the model, it can be reused for *every* mass
admissible for the literal compact-Haar boundary Poincare form. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence
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

namespace PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence

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

/-- Every positive element of the intrinsic literal-Wilson admissible mass set
canonically gives the defect-free direct gap certificate, with no additional
quantitative input. -/
noncomputable def toDirectGapCertificate
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    {m : ℝ}
    (hm : m ∈
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant)
    (hmpos : 0 < m) :
    PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectGapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant where
  boundedAnalysis := B
  mass := m
  mass_pos := hmpos
  eventually_boundary_poincare := by
    exact hm.2

/-- The same mass-independent cross-scale convergence packages the direct gap
certificate for any positive admissible mass. -/
noncomputable def toDirectCommonCarrierGapTransfer
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    {m : ℝ}
    (hm : m ∈
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant)
    (hmpos : 0 < m) :
    PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryPoincareDirectCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant
      (G.toDirectGapCertificate hm hmpos) P T where
  approximateExcitation := G.approximateExcitation
  approximate_norm_tendsto := G.approximate_norm_tendsto
  evolved_norm_tendsto := by
    intro t psi
    simpa [toDirectGapCertificate] using G.evolved_norm_tendsto t psi

/-- Nonnegativity of the actual graph-closed OS Hamiltonian makes zero an
admissible continuum Rayleigh lower bound. -/
theorem zero_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 ≤ T.physicalYangMillsMass := by
  apply T.rayleighLowerBound_le_physicalYangMillsMass W
  intro psi _hpsiNonzero _horthogonal
  simpa using T.closedRightHamiltonian_inner_nonneg psi

/-- Every mass selected intrinsically by the literal finite Wilson boundary
Poincare form lies below the variational physical Yang--Mills mass.

For positive masses this is the defect-free genuine floor-time transfer from
#1542.  The zero endpoint follows from nonnegativity of the actual graph-closed
Hamiltonian. -/
theorem admissibleMass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    {m : ℝ}
    (hm : m ∈
      physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant) :
    m ≤ T.physicalYangMillsMass := by
  by_cases hmzero : m = 0
  · simpa [hmzero] using G.zero_le_physicalYangMillsMass W
  · have hmnonneg : 0 ≤ m := hm.1
    have hmpos : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmzero)
    exact
      (G.toDirectCommonCarrierGapTransfer hm hmpos).mass_le_physicalYangMillsMass
        hP W

/-- The intrinsic literal-Wilson admissible mass set is automatically bounded
above by the actual variational physical mass. -/
theorem boundaryPoincareAdmissibleMassSet_bddAbove
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    BddAbove
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant) := by
  refine ⟨T.physicalYangMillsMass, ?_⟩
  intro m hm
  exact G.admissibleMass_le_physicalYangMillsMass hP W hm

/-- Therefore the model-derived intrinsic Wilson boundary optimal mass is no
larger than the actual graph-closed variational physical Yang--Mills mass.

This theorem contains no selected certificate mass and no numerical target.
The reverse inequality is the genuine sharp recovery/form-convergence frontier. -/
theorem boundaryPoincareOptimalMass_le_physicalYangMillsMass
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence
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
    G.admissibleMass_le_physicalYangMillsMass hP W hm

end PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierConvergence

end MathlibAnalytic
end MGAP4D

end