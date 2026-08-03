import MGAP4D.MathlibAnalytic.FiniteDimensionalNormOneGroundSpectrum
import Mathlib.Data.Finset.Max
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

/-- Finite set of all strictly excited support-Hamiltonian energies. -/
noncomputable def excitedEnergyValues : Finset ℝ :=
  Finset.univ.image
    (fun i : D.ExcitedSpectralIndex =>
      D.positiveSpectralEnergy i.toPositive)

/-- The excited energy set is nonempty whenever the excited index is. -/
theorem excitedEnergyValues_nonempty
    [Nonempty D.ExcitedSpectralIndex] :
    D.excitedEnergyValues.Nonempty := by
  classical
  let i : D.ExcitedSpectralIndex := Classical.choice inferInstance
  refine ⟨D.positiveSpectralEnergy i.toPositive, ?_⟩
  simp [excitedEnergyValues]

/-- Exact finite-volume excitation gap: the minimum strictly positive support
energy.  This is defined only when a strictly excited mode exists. -/
noncomputable def excitationGap
    [Nonempty D.ExcitedSpectralIndex] : ℝ :=
  D.excitedEnergyValues.min' D.excitedEnergyValues_nonempty

/-- The excitation gap lies below every excited energy. -/
theorem excitationGap_le_energy
    [Nonempty D.ExcitedSpectralIndex]
    (i : D.ExcitedSpectralIndex) :
    D.excitationGap ≤ D.positiveSpectralEnergy i.toPositive := by
  classical
  unfold excitationGap
  apply Finset.min'_le
  simp [excitedEnergyValues]

/-- The finite excited-sector gap is strictly positive. -/
theorem excitationGap_pos
    [Nonempty D.ExcitedSpectralIndex] :
    0 < D.excitationGap := by
  classical
  have hmem : D.excitationGap ∈ D.excitedEnergyValues := by
    unfold excitationGap
    exact Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
  rw [← hi]
  exact D.excitedSpectralEnergy_pos i

/-- One-step Hamiltonian weight of every excited mode is bounded by the exact
gap weight. -/
theorem exp_neg_excitedEnergy_le_exp_neg_gap
    [Nonempty D.ExcitedSpectralIndex]
    (i : D.ExcitedSpectralIndex) :
    Real.exp (-D.positiveSpectralEnergy i.toPositive) ≤
      Real.exp (-D.excitationGap) := by
  exact Real.exp_le_exp.mpr (neg_le_neg (D.excitationGap_le_energy i))

/-- At every natural time, each excited support coordinate decays at least with
the exact finite excitation-gap weight. -/
theorem excitedSemigroup_coordinate_abs_le_gap
    [Nonempty D.ExcitedSpectralIndex]
    (n : ℕ)
    (x : D.PositiveSpectralSpace)
    (i : D.ExcitedSpectralIndex) :
    |D.positiveSpectralSemigroup n x i.toPositive| ≤
      (Real.exp (-D.excitationGap)) ^ n * |x i.toPositive| := by
  rw [D.positiveSpectralSemigroup_eq_exp_neg_energy_pow_apply]
  rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hp :
      (Real.exp (-D.positiveSpectralEnergy i.toPositive)) ^ n ≤
        (Real.exp (-D.excitationGap)) ^ n := by
    exact pow_le_pow_left₀ (Real.exp_pos _).le
      (D.exp_neg_excitedEnergy_le_exp_neg_gap i)
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

/-- The exact gap weight is strictly below one at every positive natural time. -/
theorem exp_neg_excitationGap_pow_lt_one
    [Nonempty D.ExcitedSpectralIndex]
    {n : ℕ}
    (hn : 0 < n) :
    (Real.exp (-D.excitationGap)) ^ n < 1 := by
  have hbase : Real.exp (-D.excitationGap) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos (D.excitationGap_pos))
  exact pow_lt_one₀ (Real.exp_pos _).le hbase hn.ne'

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
