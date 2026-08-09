import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryOptimalMassToPhysical
import Mathlib.Tactic

noncomputable section

open Set
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer

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

/-- Every mass admitted by the intrinsic literal compact-Haar Wilson boundary
Poincare problem is itself an admissible Rayleigh coercivity constant for the
actual graph-closed physical Yang--Mills Hamiltonian.

This is stronger than only comparing each mass numerically with
`physicalYangMillsMass`: it embeds the complete finite-Wilson admissible set
into the intrinsic continuum Rayleigh lower-bound set.  The endpoint `m = 0`
follows from Hamiltonian nonnegativity; the positive case uses the defect-free
genuine floor-time Wilson transfer. -/
theorem admissibleMass_mem_physicalYangMillsRayleighLowerBoundSet
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized)
    {m : ℝ}
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    m ∈ T.physicalYangMillsRayleighLowerBoundSet := by
  by_cases hzero : m = 0
  · subst m
    intro psi _hpsiNonzero _horthogonal
    simpa using T.closedRightHamiltonian_inner_nonneg psi
  · have hmPos : 0 < m := lt_of_le_of_ne hm.1 (Ne.symm hzero)
    exact
      (G.toDirectCommonCarrierGapTransferOfAdmissible m hmPos hm)
        |>.mass_mem_physicalYangMillsRayleighLowerBoundSet hP

/-- Set-level finite-to-continuum coercivity inclusion:

`Wilson admissible masses ⊆ actual H_phys Rayleigh lower bounds`.

No distinguished mass, exact value, decay parameter, or normalization constant
appears in the statement. -/
theorem boundaryPoincareAdmissibleMassSet_subset_rayleighLowerBoundSet
    (G : PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant B P T)
    (hP : P.IsNormalized) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant ⊆
      T.physicalYangMillsRayleighLowerBoundSet := by
  intro m hm
  exact G.admissibleMass_mem_physicalYangMillsRayleighLowerBoundSet hP hm

end PhysicalYangMillsEvenPeriodicWilsonOSLiteralBoundaryMassFreeCommonCarrierTransfer

end MathlibAnalytic
end MGAP4D

end