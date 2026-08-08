import MGAP4D.MathlibAnalytic.FiniteDimensionalSpectralDefectExcitedSupportNontriviality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- An injective finite symmetric positive contraction that is not the identity
must carry a strictly excited eigenvalue in `(0,1)`.

If the excited sector were empty, Package AA's generic spectral theorem would
force `P_ground = T`.  But `T (P_ground x) = P_ground x`; after the equality
this reads `T (T x) = T x`, and injectivity gives `T x = x` for every `x`. -/
theorem nonempty_excitedSpectralIndex_of_operator_injective_of_ne_one
    (hinj : Function.Injective D.operator)
    (hne : D.operator ≠ 1) :
    Nonempty D.ExcitedSpectralIndex := by
  classical
  by_contra hempty
  have hEq : D.groundSpectralProjector = D.operator :=
    D.groundSpectralProjector_eq_operator_of_not_nonempty_excitedSpectralIndex
      hempty
  apply hne
  apply ContinuousLinearMap.ext
  intro x
  have hfixed := D.operator_groundSpectralProjector x
  rw [hEq] at hfixed
  have hx : D.operator x = x := hinj hfixed
  simpa using hx

/-- The same two hypotheses already imply that the positive-support
Hamiltonian has a strictly positive spectral energy. -/
theorem exists_positiveSpectralEnergy_of_operator_injective_of_ne_one
    (hinj : Function.Injective D.operator)
    (hne : D.operator ≠ 1) :
    ∃ i : D.ExcitedSpectralIndex,
      0 < D.positiveSpectralEnergy i.toPositive :=
  D.exists_excited_positiveSpectralEnergy
    (D.nonempty_excitedSpectralIndex_of_operator_injective_of_ne_one hinj hne)

/-- In particular the positive-support Hamiltonian cannot be the zero
operator. -/
theorem positiveSpectralHamiltonian_ne_zero_of_operator_injective_of_ne_one
    (hinj : Function.Injective D.operator)
    (hne : D.operator ≠ 1) :
    D.positiveSpectralHamiltonian ≠ 0 :=
  D.positiveSpectralHamiltonian_ne_zero_of_nonempty_excitedSpectralIndex
    (D.nonempty_excitedSpectralIndex_of_operator_injective_of_ne_one hinj hne)

/-- Audit-visible generic receipt for the injective/nonidentity route. -/
structure InjectiveNonidentityExcitedSupportPackage where
  operatorInjective : Function.Injective D.operator
  operatorNonidentity : D.operator ≠ 1
  excitedNonempty : Nonempty D.ExcitedSpectralIndex
  positiveEnergy :
    ∃ i : D.ExcitedSpectralIndex,
      0 < D.positiveSpectralEnergy i.toPositive
  supportHamiltonianNonzero : D.positiveSpectralHamiltonian ≠ 0

/-- Construct the generic receipt from the two operator-level hypotheses. -/
noncomputable def injectiveNonidentityExcitedSupportPackage
    (hinj : Function.Injective D.operator)
    (hne : D.operator ≠ 1) :
    D.InjectiveNonidentityExcitedSupportPackage :=
  { operatorInjective := hinj
    operatorNonidentity := hne
    excitedNonempty :=
      D.nonempty_excitedSpectralIndex_of_operator_injective_of_ne_one hinj hne
    positiveEnergy :=
      D.exists_positiveSpectralEnergy_of_operator_injective_of_ne_one hinj hne
    supportHamiltonianNonzero :=
      D.positiveSpectralHamiltonian_ne_zero_of_operator_injective_of_ne_one
        hinj hne }

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
