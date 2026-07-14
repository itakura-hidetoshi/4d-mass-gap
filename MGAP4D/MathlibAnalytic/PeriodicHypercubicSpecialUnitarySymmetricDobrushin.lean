import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryExplicitDobrushin

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Shared plaquettes are symmetric in the two physical links for the canonical
compact-oriented `SU(N)` density-ratio system. -/
theorem specialUnitaryContinuousCompactOriented_sharedPlaquettes_comm
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : geometry.Edge) :
    (specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg).base.sharedPlaquettes target source =
    (specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg).base.sharedPlaquettes source target := by
  classical
  apply Finset.ext
  intro p
  rw [compact_oriented_mem_sharedPlaquettes_iff,
    compact_oriented_mem_sharedPlaquettes_iff]
  constructor
  · rintro ⟨hTarget, hSource⟩
    exact ⟨hSource, hTarget⟩
  · rintro ⟨hSource, hTarget⟩
    exact ⟨hTarget, hSource⟩

/-- The explicit compact-Haar `SU(N)` shared-plaquette influence matrix is
symmetric. -/
theorem specialUnitaryCompactOrientedSharedPlaquetteInfluence_symm
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : geometry.Edge) :
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
        geometry N hN beta beta_nonneg target source =
      specialUnitaryCompactOrientedSharedPlaquetteInfluence
        geometry N hN beta beta_nonneg source target := by
  classical
  by_cases hEq : target = source
  · subst source
    rfl
  · have hEq' : source ≠ target := Ne.symm hEq
    unfold specialUnitaryCompactOrientedSharedPlaquetteInfluence
    rw [if_neg hEq, if_neg hEq',
      specialUnitaryContinuousCompactOriented_sharedPlaquettes_comm]

/-- The periodic compact-Haar `SU(N)` influence matrix is symmetric on physical
links. -/
theorem periodicHypercubicSpecialUnitary_influence_symm
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n) :
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg target source =
      specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg source target :=
  specialUnitaryCompactOrientedSharedPlaquetteInfluence_symm
    (periodicHypercubicFiniteOrientedGeometry n)
    N hN beta beta_nonneg target source

/-- By symmetry, every column sum equals the corresponding row sum. -/
theorem periodicHypercubicSpecialUnitary_influence_columnSum_eq_rowSum
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (source : PeriodicHypercubicEdge n) :
    (∑ target : PeriodicHypercubicEdge n,
      specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg target source) =
      ∑ target : PeriodicHypercubicEdge n,
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg source target := by
  classical
  apply Finset.sum_congr rfl
  intro target _hTarget
  exact periodicHypercubicSpecialUnitary_influence_symm
    n N hN beta beta_nonneg target source

/-- Every column of the explicit periodic `SU(N)` influence matrix obeys the
same volume-uniform `18 * eta` bound as every row. -/
theorem periodicHypercubicSpecialUnitary_influence_columnSum_le
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (source : PeriodicHypercubicEdge n) :
    (∑ target : PeriodicHypercubicEdge n,
      specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg target source) ≤
      18 * periodicHypercubicSpecialUnitaryDobrushinEta beta := by
  rw [periodicHypercubicSpecialUnitary_influence_columnSum_eq_rowSum]
  exact periodicHypercubicSpecialUnitary_influence_rowSum_le
    n N hn hN beta beta_nonneg source

/-- The symmetric periodic `SU(N)` influence matrix contracts every nonnegative
link profile in `ℓ¹` by the same volume-independent Dobrushin coefficient. -/
theorem periodicHypercubicSpecialUnitary_influence_l1_le
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (profile : PeriodicHypercubicEdge n → ℝ)
    (profile_nonneg : ∀ source, 0 ≤ profile source) :
    (∑ target : PeriodicHypercubicEdge n,
      ∑ source : PeriodicHypercubicEdge n,
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg target source * profile source) ≤
      (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta) *
        ∑ source : PeriodicHypercubicEdge n, profile source := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ source : PeriodicHypercubicEdge n,
      ∑ target : PeriodicHypercubicEdge n,
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg target source * profile source) ≤
        ∑ source : PeriodicHypercubicEdge n,
          (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta) *
            profile source := by
      apply Finset.sum_le_sum
      intro source _hSource
      rw [Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (periodicHypercubicSpecialUnitary_influence_columnSum_le
          n N hn hN beta beta_nonneg source)
        (profile_nonneg source)
    _ = (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta) *
        ∑ source : PeriodicHypercubicEdge n, profile source := by
      rw [Finset.mul_sum]

end

end MathlibAnalytic
end MGAP4D
