import MGAP4D.MathlibAnalytic.FiniteOneDimensionalGroundSpectralProjectorRankOne
import MGAP4D.MathlibAnalytic.FiniteDimensionalGroundExcitationSupportDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- If no strictly excited transfer mode exists, every canonical eigenvalue is
zero or one, so the transfer is exactly its ground spectral projector. -/
theorem groundSpectralProjector_eq_operator_of_not_nonempty_excitedSpectralIndex
    (hempty : ¬ Nonempty D.ExcitedSpectralIndex) :
    D.groundSpectralProjector = D.operator := by
  apply ContinuousLinearMap.ext
  intro x
  rw [← D.eigenbasis.sum_repr' x]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [D.groundSpectralProjector_apply_eigenbasis,
    D.operator_apply_eigenbasis]
  have hcoef :
      D.groundSpectralProjectorCoefficient i = D.eigenvalue i := by
    rcases D.eigenvalue_trichotomy i with hz | he | hg
    · simp [groundSpectralProjectorCoefficient, hz]
    · exact (hempty ⟨⟨i, he⟩⟩).elim
    · simp [groundSpectralProjectorCoefficient, hg]
  rw [hcoef]

/-- A nonzero actual spectral defect `P_ground - T` forces the existence of a
strictly positive transfer eigenvalue strictly below one. -/
theorem nonempty_excitedSpectralIndex_of_groundSpectralProjector_sub_operator_ne_zero
    (hne : D.groundSpectralProjector - D.operator ≠ 0) :
    Nonempty D.ExcitedSpectralIndex := by
  by_contra hempty
  apply hne
  rw [D.groundSpectralProjector_eq_operator_of_not_nonempty_excitedSpectralIndex hempty]
  simp

/-- Conversely, one nonzero eigenvector with eigenvalue in `(0,1)` already
forces the ground spectral defect to be nonzero.  This formulation is useful
when transporting an ambient excited mode into an invariant compression. -/
theorem groundSpectralProjector_sub_operator_ne_zero_of_strict_eigenvector
    (v : E)
    (hv : v ≠ 0)
    (λ : ℝ)
    (hλpos : 0 < λ)
    (hλlt : λ < 1)
    (heig : D.operator v = λ • v) :
    D.groundSpectralProjector - D.operator ≠ 0 := by
  intro hzero
  have hEq : D.groundSpectralProjector = D.operator :=
    sub_eq_zero.mp hzero
  have hfixed := D.operator_groundSpectralProjector v
  rw [hEq] at hfixed
  rw [heig, map_smul, heig, smul_smul] at hfixed
  have hinner := congrArg (fun w : E => inner ℝ w v) hfixed
  simp only [real_inner_smul_left] at hinner
  have hvpos : 0 < inner ℝ v v := real_inner_self_pos.mpr hv
  nlinarith

/-- A nonempty excited sector contains a strictly positive support-Hamiltonian
energy. -/
theorem exists_excited_positiveSpectralEnergy
    (hex : Nonempty D.ExcitedSpectralIndex) :
    ∃ i : D.ExcitedSpectralIndex,
      0 < D.positiveSpectralEnergy i.toPositive := by
  let i : D.ExcitedSpectralIndex := Classical.choice hex
  exact ⟨i, D.excitedSpectralEnergy_pos i⟩

/-- A nonempty excited sector makes the positive-support Hamiltonian genuinely
nonzero. -/
theorem positiveSpectralHamiltonian_ne_zero_of_nonempty_excitedSpectralIndex
    (hex : Nonempty D.ExcitedSpectralIndex) :
    D.positiveSpectralHamiltonian ≠ 0 := by
  let i : D.ExcitedSpectralIndex := Classical.choice hex
  let e : D.PositiveSpectralSpace := EuclideanSpace.single i.toPositive 1
  intro hzero
  have hz : D.positiveSpectralHamiltonian e = 0 := by
    rw [hzero]
    rfl
  have hcoord := congrArg (fun x : D.PositiveSpectralSpace => x i.toPositive) hz
  change D.positiveSpectralEnergy i.toPositive * e i.toPositive = 0 at hcoord
  have heval : e i.toPositive = 1 := by
    simp [e]
  rw [heval, mul_one] at hcoord
  exact (ne_of_gt (D.excitedSpectralEnergy_pos i)) hcoord

/-- Audit-visible generic receipt: a nonzero ground spectral defect carries a
strictly excited transfer mode and a nontrivial positive-support Hamiltonian. -/
structure SpectralDefectExcitedSupportPackage where
  excitedNonempty : Nonempty D.ExcitedSpectralIndex
  positiveEnergy :
    ∃ i : D.ExcitedSpectralIndex,
      0 < D.positiveSpectralEnergy i.toPositive
  supportHamiltonianNonzero : D.positiveSpectralHamiltonian ≠ 0

/-- Construct the generic spectral-defect-to-excited-support receipt. -/
noncomputable def spectralDefectExcitedSupportPackage
    (hne : D.groundSpectralProjector - D.operator ≠ 0) :
    D.SpectralDefectExcitedSupportPackage := by
  let hex :=
    D.nonempty_excitedSpectralIndex_of_groundSpectralProjector_sub_operator_ne_zero hne
  exact
    { excitedNonempty := hex
      positiveEnergy := D.exists_excited_positiveSpectralEnergy hex
      supportHamiltonianNonzero :=
        D.positiveSpectralHamiltonian_ne_zero_of_nonempty_excitedSpectralIndex hex }

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
