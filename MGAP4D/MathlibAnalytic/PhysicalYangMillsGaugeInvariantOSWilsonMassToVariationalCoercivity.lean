import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOptimalRayleighCoercivity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- A mass transferred from the actual finite Wilson OS Hilbert spaces through
the common continuum carrier is an admissible Rayleigh coercivity constant for
the graph-closed physical Yang--Mills Hamiltonian.

This places the finite-to-continuum Wilson gap route directly inside the
intrinsic variational lower-bound set introduced after #1529/#1531.  The
certificate mass is therefore not merely a decay label: it is a genuine lower
bound for the actual `H_phys` excitation spectrum. -/
theorem mass_mem_physicalYangMillsRayleighLowerBoundSet
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hP : P.IsNormalized) :
    G.mass ∈ T.physicalYangMillsRayleighLowerBoundSet := by
  intro psi _hpsi horthogonal
  exact A.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    hP psi horthogonal

/-- Consequently every mass supplied by the actual Wilson common-carrier gap
transfer lies below the variational physical Yang--Mills mass.

No numerical target appears: this is the monotone comparison needed before an
optimal finite Wilson coercivity can be identified with the exact continuum
mass. -/
theorem mass_le_physicalYangMillsMass
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    G.mass ≤ T.physicalYangMillsMass := by
  exact T.rayleighLowerBound_le_physicalYangMillsMass W
    (A.mass_mem_physicalYangMillsRayleighLowerBoundSet hP)

/-- If the complete Wilson/continuum construction proves that its transferred
mass is the greatest admissible actual-Hamiltonian coercivity constant, then it
is theorem-equal to the variational physical Yang--Mills mass.

The equality is derived from optimality; it is not a field of the Wilson gap
certificate.  This is the exact endpoint to which a non-circular numerical
normalization theorem must connect. -/
theorem physicalYangMillsMass_eq_mass_of_isGreatest
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    (hGreatest :
      IsGreatest T.physicalYangMillsRayleighLowerBoundSet G.mass) :
    T.physicalYangMillsMass = G.mass := by
  exact T.physicalYangMillsMass_eq_of_isGreatest_rayleighLowerBoundSet
    W hGreatest

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
