import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingStronglyContinuousSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonExcitationStrongLimit
import MGAP4D.MathlibAnalytic.FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A right Hamiltonian value is equivalently the limit of the signed
Hamiltonian difference quotient. -/
theorem HasRightHamiltonianValue.tendsto_rightHamiltonianDifferenceQuotient
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi eta : P.PhysicalHilbert}
    (h : T.HasRightHamiltonianValue psi eta) :
    Tendsto (fun t : NNReal => T.rightHamiltonianDifferenceQuotient psi t)
      (nhdsWithin 0 (Ioi 0)) (nhds eta) := by
  unfold HasRightHamiltonianValue HasRightGeneratorValue at h
  have hneg := h.neg
  simpa only [rightHamiltonianDifferenceQuotient_eq_neg, neg_neg] using hneg

/-- The actual finite Wilson OS semigroup is strongly continuous, and the
isometric realization of the finite Hamiltonian sector intertwines its right
Hamiltonian with the abstract finite-dimensional Wilson Hamiltonian.

This is a generator-level structural input.  It is strictly local at time zero
and does not assume a finite-semigroup exponential eigenaction. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorIntertwiningData
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℕ → ℝ}
    {hbeta : ∀ n m, 0 ≤ beta n m}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n)}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n) B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n) B hInvariant C}
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n)
        B hInvariant P T C Q)
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W) where
  strongContinuity :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingStrongContinuityData C
  realization :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonExcitationRealizationData
      A F
  finiteRealization_mem_rightGeneratorDomain :
    ∀ n phi,
      realization.finiteRealization n phi ∈
        (strongContinuity.finiteStronglyContinuousPhysicalSemigroup n).rightGeneratorDomain
  finiteRightHamiltonian_realization :
    ∀ n phi,
      let Tn := strongContinuity.finiteStronglyContinuousPhysicalSemigroup n
      Tn.rightHamiltonian
          ⟨realization.finiteRealization n phi,
            finiteRealization_mem_rightGeneratorDomain n phi⟩ =
        realization.finiteRealization n (F.hamiltonian n phi)

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorIntertwiningData

variable
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℕ → ℝ}
    {hbeta : ∀ n m, 0 ≤ beta n m}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n)}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n) B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n) B hInvariant C}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n)
        B hInvariant P T C Q}
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W}

abbrev GeneratorIntertwiningData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n)
        B hInvariant P T C Q)
    (F : FiniteWilsonOSAutomaticExactGapFiniteDimensionalHamiltonianContractionData W) :=
  PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorIntertwiningData
    A F

/-- The strongly continuous actual finite Wilson OS semigroup at one scale. -/
noncomputable def finiteStrongSemigroup
    (R : GeneratorIntertwiningData A F)
    (n : ℕ) :=
  R.strongContinuity.finiteStronglyContinuousPhysicalSemigroup n

/-- A realized finite Hamiltonian vector bundled into the actual finite OS right
generator domain. -/
noncomputable def realizedDomainPoint
    (R : GeneratorIntertwiningData A F)
    (n : ℕ) (phi : F.StateSpace) :
    (R.finiteStrongSemigroup n).rightGeneratorDomain :=
  ⟨R.realization.finiteRealization n phi,
    R.finiteRealization_mem_rightGeneratorDomain n phi⟩

@[simp] theorem realizedDomainPoint_coe
    (R : GeneratorIntertwiningData A F)
    (n : ℕ) (phi : F.StateSpace) :
    (R.realizedDomainPoint n phi :
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN (fun n => beta n n) (fun n => hbeta n n)
          B hInvariant n) =
      R.realization.finiteRealization n phi :=
  rfl

/-- The actual finite OS right Hamiltonian agrees with the realized abstract
finite Wilson Hamiltonian on every vector of the finite sector. -/
theorem rightHamiltonian_realizedDomainPoint
    (R : GeneratorIntertwiningData A F)
    (n : ℕ) (phi : F.StateSpace) :
    (R.finiteStrongSemigroup n).rightHamiltonian
        (R.realizedDomainPoint n phi) =
      R.realization.finiteRealization n (F.hamiltonian n phi) := by
  simpa [finiteStrongSemigroup, realizedDomainPoint] using
    R.finiteRightHamiltonian_realization n phi

/-- Every realized finite-sector vector has the right Hamiltonian value obtained
by realizing the abstract finite Hamiltonian action. -/
theorem hasRightHamiltonianValue_realization
    (R : GeneratorIntertwiningData A F)
    (n : ℕ) (phi : F.StateSpace) :
    (R.finiteStrongSemigroup n).HasRightHamiltonianValue
      (R.realization.finiteRealization n phi)
      (R.realization.finiteRealization n (F.hamiltonian n phi)) := by
  have h :=
    (R.finiteStrongSemigroup n).rightHamiltonian_hasRightHamiltonianValue
      (R.realizedDomainPoint n phi)
  rw [R.rightHamiltonian_realizedDomainPoint n phi] at h
  exact h

/-- A selected finite Wilson Hamiltonian eigenvector becomes an actual finite OS
right-Hamiltonian eigenvector with the same energy. -/
theorem hasRightHamiltonianValue_spectralVector
    {α : Type*}
    [DecidableEq α]
    (R : GeneratorIntertwiningData A F)
    (n : ℕ)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ)
    (V : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      F n value nodes orderCap)
    (k : V.SpectralIndex) :
    (R.finiteStrongSemigroup n).HasRightHamiltonianValue
      (R.realization.finiteRealization n (V.spectralVector k))
      (V.spectralValue k •
        R.realization.finiteRealization n (V.spectralVector k)) := by
  have h := R.hasRightHamiltonianValue_realization n (V.spectralVector k)
  rw [V.hamiltonian_apply_spectralVector, map_smul] at h
  exact h

/-- Equivalently, the signed actual finite OS difference quotient of every
selected Wilson eigenvector converges to its finite Hamiltonian eigenvalue
multiple. -/
theorem rightHamiltonianDifferenceQuotient_tendsto_spectralVector
    {α : Type*}
    [DecidableEq α]
    (R : GeneratorIntertwiningData A F)
    (n : ℕ)
    (value : α → ℝ)
    (nodes : Finset α)
    (orderCap : ℕ)
    (V : FiniteWilsonFiniteDimensionalHamiltonianConfluentSpectralWitnessData
      F n value nodes orderCap)
    (k : V.SpectralIndex) :
    Tendsto
      (fun t : NNReal =>
        (R.finiteStrongSemigroup n).rightHamiltonianDifferenceQuotient
          (R.realization.finiteRealization n (V.spectralVector k)) t)
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (V.spectralValue k •
          R.realization.finiteRealization n (V.spectralVector k))) :=
  (R.hasRightHamiltonianValue_spectralVector n value nodes orderCap V k).tendsto_rightHamiltonianDifferenceQuotient
    (R.finiteStrongSemigroup n)

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierFiniteWilsonGeneratorIntertwiningData

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
