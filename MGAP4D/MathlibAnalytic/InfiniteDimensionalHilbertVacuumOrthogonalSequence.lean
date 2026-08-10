import MGAP4D.MathlibAnalytic.SeparableHilbertVacuumOrthogonalSequenceIsometry
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

universe u v

/-- A countable orthonormal excitation sequence orthogonal to a distinguished
vacuum.  This is the concrete target geometry consumed by the separable-source
isometry theorem of `SeparableHilbertVacuumOrthogonalSequenceIsometry`. -/
structure VacuumOrthogonalOrthonormalSequenceData
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (vacuum : K) where
  excitation : ℕ → K
  excitation_orthonormal : Orthonormal ℝ excitation
  vacuum_orthogonal_excitation : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0

/-- A unit vector in an infinite-dimensional real Hilbert space has a countable
orthonormal sequence in its orthogonal complement.

The proof is entirely Hilbert-geometric.  Extend the singleton vacuum to a
Mathlib Hilbert basis.  The basis index set cannot be finite, since a finite
Hilbert basis would yield a finite-dimensional vector space.  Removing the
single vacuum vector leaves an infinite set; `Infinite.natEmbedding` then
selects a countable subfamily.  Orthonormality and vacuum orthogonality are
inherited from the ambient Hilbert basis. -/
theorem vacuumOrthogonalOrthonormalSequenceData_nonempty_of_not_finiteDimensional
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K]
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (hInfinite : ¬ FiniteDimensional ℝ K) :
    Nonempty (VacuumOrthogonalOrthonormalSequenceData vacuum) := by
  classical
  have hs : Orthonormal ℝ ((↑) : ({vacuum} : Set K) → K) := by
    rw [orthonormal_subsingleton_iff]
    intro x
    have hx : (x : K) = vacuum := Set.mem_singleton_iff.mp x.property
    simpa [hx] using hVacuum
  obtain ⟨w, b, hsub, hb⟩ := hs.exists_hilbertBasis_extension
  have hwInfinite : w.Infinite := by
    intro hwFinite
    letI : Fintype w := hwFinite.fintype
    apply hInfinite
    exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  have hAwayInfinite : (w \ {vacuum}).Infinite := by
    intro hAwayFinite
    exact hwInfinite (Set.Finite.of_sdiff hAwayFinite (Set.finite_singleton vacuum))
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

/-- Noncomputably select the vacuum-orthogonal orthonormal excitation sequence
forced by infinite Hilbert dimension. -/
noncomputable def vacuumOrthogonalOrthonormalSequenceDataOfNotFiniteDimensional
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K]
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (hInfinite : ¬ FiniteDimensional ℝ K) :
    VacuumOrthogonalOrthonormalSequenceData vacuum :=
  Classical.choice
    (vacuumOrthogonalOrthonormalSequenceData_nonempty_of_not_finiteDimensional
      vacuum hVacuum hInfinite)

/-- A separable source Hilbert space therefore embeds isometrically into any
infinite-dimensional target Hilbert space, with prescribed unit distinguished
vectors matched exactly. -/
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

/-- The infinite-dimensional-target construction preserves the distinguished
unit vectors exactly. -/
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
