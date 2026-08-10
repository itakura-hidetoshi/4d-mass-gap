import MGAP4D.MathlibAnalytic.SeparableHilbertVacuumOrthogonalSequenceIsometry
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

universe u v

structure VacuumOrthogonalOrthonormalSequenceData
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (vacuum : K) where
  excitation : ℕ → K
  excitation_orthonormal : Orthonormal ℝ excitation
  vacuum_orthogonal_excitation : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0

/-- A unit vector in an infinite-dimensional real Hilbert space has a countable
orthonormal sequence in its orthogonal complement. -/
theorem vacuumOrthogonalOrthonormalSequenceData_nonempty_of_not_finiteDimensional
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K]
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (hInfinite : ¬ FiniteDimensional ℝ K) :
    Nonempty (VacuumOrthogonalOrthonormalSequenceData vacuum) := by
  classical
  have hs : Orthonormal ℝ ((↑) : ({vacuum} : Set K) → K) := by
    constructor
    · intro x
      have hx : (x : K) = vacuum := Set.mem_singleton_iff.mp x.property
      simpa [hx] using hVacuum
    · exact Subsingleton.pairwise
  obtain ⟨w, b, hsub, hb⟩ := hs.exists_hilbertBasis_extension
  have hwInfinite : w.Infinite := by
    intro hwFinite
    letI : Fintype w := hwFinite.fintype
    apply hInfinite
    exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hAwayInfinite : (w \ {vacuum}).Infinite := by
    intro hAwayFinite
    apply hwInfinite
    apply (hAwayFinite.union (Set.finite_singleton vacuum)).subset
    intro x hx
    by_cases hxVacuum : x = vacuum
    · exact Or.inr (by simpa [hxVacuum])
    · exact Or.inl ⟨hx, by simpa using hxVacuum⟩
  let awayIndex : ℕ ↪ (w \ {vacuum}) :=
    Infinite.natEmbedding (w \ {vacuum}) hAwayInfinite
  let includeAway : (w \ {vacuum}) ↪ w :=
    ⟨fun x => ⟨x.1, x.2.1⟩, by
      intro x y hxy
      apply Subtype.ext
      exact congrArg Subtype.val hxy⟩
  let sequenceIndex : ℕ ↪ w := awayIndex.trans includeAway
  let excitation : ℕ → K := fun n => b (sequenceIndex n)
  have hExcitation : Orthonormal ℝ excitation := by
    exact b.orthonormal.comp sequenceIndex sequenceIndex.injective
  let vacuumIndex : w := ⟨vacuum, hsub (by simp)⟩
  have hbVacuum : b vacuumIndex = vacuum := by
    simpa [vacuumIndex] using congr_fun hb vacuumIndex
  have hOrthogonal : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0 := by
    intro n
    have hne : vacuumIndex ≠ sequenceIndex n := by
      intro hEq
      have hval : vacuum = (awayIndex n : K) := by
        simpa [vacuumIndex, sequenceIndex, includeAway] using
          congrArg Subtype.val hEq
      exact (awayIndex n).property.2 (by simpa using hval.symm)
    have hinner := b.orthonormal.inner_eq_zero hne
    simpa [excitation, hbVacuum] using hinner
  exact ⟨{
    excitation := excitation
    excitation_orthonormal := hExcitation
    vacuum_orthogonal_excitation := hOrthogonal }⟩

noncomputable def vacuumOrthogonalOrthonormalSequenceDataOfNotFiniteDimensional
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K]
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (hInfinite : ¬ FiniteDimensional ℝ K) :
    VacuumOrthogonalOrthonormalSequenceData vacuum :=
  Classical.choice
    (vacuumOrthogonalOrthonormalSequenceData_nonempty_of_not_finiteDimensional
      vacuum hVacuum hInfinite)

noncomputable def distinguishedVectorLinearIsometryOfSeparableInfiniteDimensionalTarget
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (x : H) (hx : ‖x‖ = 1)
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (hInfinite : ¬ FiniteDimensional ℝ K) :
    H →ₗᵢ[ℝ] K := by
  let J := vacuumOrthogonalOrthonormalSequenceDataOfNotFiniteDimensional
    vacuum hVacuum hInfinite
  exact distinguishedVectorLinearIsometryOfSeparableVacuumOrthogonalSequence
    x hx vacuum hVacuum
    J.excitation J.excitation_orthonormal J.vacuum_orthogonal_excitation

@[simp] theorem distinguishedVectorLinearIsometryOfSeparableInfiniteDimensionalTarget_apply
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (x : H) (hx : ‖x‖ = 1)
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (hInfinite : ¬ FiniteDimensional ℝ K) :
    distinguishedVectorLinearIsometryOfSeparableInfiniteDimensionalTarget
      x hx vacuum hVacuum hInfinite x = vacuum := by
  let J := vacuumOrthogonalOrthonormalSequenceDataOfNotFiniteDimensional
    vacuum hVacuum hInfinite
  exact distinguishedVectorLinearIsometryOfSeparableVacuumOrthogonalSequence_apply
    x hx vacuum hVacuum
    J.excitation J.excitation_orthonormal J.vacuum_orthogonal_excitation

end

end MathlibAnalytic
end MGAP4D
