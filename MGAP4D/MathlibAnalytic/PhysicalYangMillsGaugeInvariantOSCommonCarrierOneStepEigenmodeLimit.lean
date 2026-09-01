import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOneStepModeFullOrbitHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

section CommonCarrier

variable
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
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- Exact finite one-step eigenmodes pass through the actual Wilson OS
common-carrier limit.

The finite eigenvalue is allowed to depend on the cutoff.  The only inputs are
its scalar convergence and the eigenvalue equation on the canonical finite
approximants supplied by `A.approximate`.  The conclusion is the continuum
one-step eigenvalue equation on the already-constructed OS physical Hilbert
space.  No Hamiltonian-domain or generator compatibility hypothesis is used. -/
theorem physicalOperator_one_apply_of_approximating_eigen
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (mu : ℕ → ℝ)
    (muLimit : ℝ)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hOne : ∀ n,
      C.finiteOperator n 1 (A.approximate n psi) =
        mu n • A.approximate n psi) :
    T.toPhysicalSemigroup.operator 1 psi = muLimit • psi := by
  have hLeft :
      Tendsto
        (fun n : ℕ =>
          A.embed n (C.finiteOperator n 1 (A.approximate n psi)))
        atTop
        (𝓝 (T.toPhysicalSemigroup.operator 1 psi)) :=
    A.evolved_tendsto 1 psi
  have hApprox :
      Tendsto
        (fun n : ℕ => A.embed n (A.approximate n psi))
        atTop
        (𝓝 psi) :=
    A.approximate_tendsto psi
  have hRight :
      Tendsto
        (fun n : ℕ => mu n • A.embed n (A.approximate n psi))
        atTop
        (𝓝 (muLimit • psi)) :=
    hmu.smul hApprox
  have hIntertwine : ∀ n : ℕ,
      A.embed n (C.finiteOperator n 1 (A.approximate n psi)) =
        mu n • A.embed n (A.approximate n psi) := by
    intro n
    rw [hOne n]
    simp
  have hRightOnLeft :
      Tendsto
        (fun n : ℕ =>
          A.embed n (C.finiteOperator n 1 (A.approximate n psi)))
        atTop
        (𝓝 (muLimit • psi)) :=
    hRight.congr' (Eventually.of_forall fun n => (hIntertwine n).symm)
  exact tendsto_nhds_unique hLeft hRightOnLeft

/-- Fixed-eigenvalue specialization of the common-carrier one-step mode
transport. -/
theorem physicalOperator_one_apply_of_fixed_approximating_eigen
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (psi : P.PhysicalHilbert)
    (mu : ℝ)
    (hOne : ∀ n,
      C.finiteOperator n 1 (A.approximate n psi) =
        mu • A.approximate n psi) :
    T.toPhysicalSemigroup.operator 1 psi = mu • psi := by
  exact physicalOperator_one_apply_of_approximating_eigen
    A psi (fun _ => mu) mu tendsto_const_nhds hOne

/-- Positive cutoff eigenvalues converging to a positive continuum eigenvalue
already generate an actual continuum vacuum-orthogonal OS Hamiltonian mode.
All unbounded-domain information is supplied downstream by the one-step mode
theorem, rather than assumed at finite cutoff. -/
theorem exists_vacuumOrthogonalClosedRightHamiltonian_mode_of_approximating_eigen
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hHamiltonianSymmetric :
      T.closedRightHamiltonian.IsFormalAdjoint T.closedRightHamiltonian)
    (psi : P.VacuumOrthogonalHilbert)
    (mu : ℕ → ℝ)
    (muLimit : ℝ)
    (hmuLimit : 0 < muLimit)
    (hmu : Tendsto mu atTop (𝓝 muLimit))
    (hOne : ∀ n,
      C.finiteOperator n 1
          (A.approximate n (psi : P.PhysicalHilbert)) =
        mu n • A.approximate n (psi : P.PhysicalHilbert)) :
    ∃ z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain,
      (z : P.VacuumOrthogonalHilbert) = psi ∧
        T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric z =
          (-Real.log muLimit) • psi := by
  have hContinuumOne :
      T.toPhysicalSemigroup.operator 1 (psi : P.PhysicalHilbert) =
        muLimit • (psi : P.PhysicalHilbert) :=
    physicalOperator_one_apply_of_approximating_eigen
      A (psi : P.PhysicalHilbert) mu muLimit hmu hOne
  let z : (T.vacuumOrthogonalClosedRightHamiltonian hHamiltonianSymmetric).domain :=
    ⟨psi,
      T.exponential_orbit_mem_vacuumOrthogonalClosedRightHamiltonianDomain
        psi (-Real.log muLimit) (by
          intro t
          simpa using
            T.physicalOperator_apply_of_one_eigen
              hInnerSymmetric (psi : P.PhysicalHilbert)
              muLimit hmuLimit hContinuumOne t)⟩
  refine ⟨z, rfl, ?_⟩
  dsimp [z]
  exact T.vacuumOrthogonalClosedRightHamiltonian_apply_of_one_eigen
    hInnerSymmetric hHamiltonianSymmetric psi muLimit hmuLimit hContinuumOne

end CommonCarrier

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
