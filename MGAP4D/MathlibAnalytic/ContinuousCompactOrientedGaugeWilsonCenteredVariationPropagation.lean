import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitarySparseConditionalTVCertificate
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinVariationPropagation
import Mathlib.Tactic

/-!
# Periodic SU(N) sparse TV as current compact Dobrushin matrix data

The current canonical tree already contains the generic compact-Haar
`ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData` carrier and its
centered variation propagation theorems.  The newer same-root periodic route
separately proves the exact compact `SU(N)` one-link conditional-TV influence,
including inactive/diagonal zeros and the volume-independent row bound

`rowSum <= 18 * q(beta)`.

This file connects those two current-canonical layers.  First it identifies the
older bounded-test shared-plaquette influence, specialized to the actual signed
periodic geometry, with the newer sparse active-TV influence.  Under the
explicit finite-volume threshold `18 * q(beta) < 1`, it then packages the
actual periodic `SU(N)` conditional laws as generic compact Dobrushin matrix
data.

The threshold is an additional high-temperature hypothesis.  Nothing here
asserts that the factorial continuum coupling sequence satisfies it, and this
static Gibbs/heat-bath Dobrushin carrier is not identified with physical OS
Euclidean time or the physical Hamiltonian gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- On an active periodic source/target pair, the concrete shared-plaquette
finset has exactly one element. -/
theorem periodicHypercubic_sharedPlaquettes_card_eq_one_of_active_current
    (n : ℕ) [NeZero n]
    (hn : 3 <= n)
    (target source : PeriodicHypercubicEdge n)
    (hActive : source ∈ periodicHypercubicActiveNeighbors n target) :
    (periodicHypercubicSharedPlaquettes n target source).card = 1 := by
  have hNe : source ≠ target :=
    (periodicHypercubic_mem_activeNeighbors_iff_for_compactSU
      n target source).mp hActive |>.2
  have hUpper :
      (periodicHypercubicSharedPlaquettes n target source).card <= 1 :=
    periodicHypercubicSharedPlaquettes_card_le_one
      n hn target source hNe
  have hWitness :=
    (periodicHypercubic_mem_activeNeighbors_iff_for_compactSU
      n target source).mp hActive |>.1
  rcases hWitness with ⟨p, hpTarget, hpSource⟩
  have hpShared :
      p ∈ periodicHypercubicSharedPlaquettes n target source :=
    (periodicHypercubic_mem_sharedPlaquettes_iff
      n target source p).mpr ⟨hpTarget, hpSource⟩
  have hLower :
      0 < (periodicHypercubicSharedPlaquettes n target source).card :=
    Finset.card_pos.mpr ⟨p, hpShared⟩
  omega

/-- The pre-existing bounded-test shared-plaquette influence is exactly the
newer sparse active-TV influence on the actual periodic `SU(N)` system. -/
theorem periodicHypercubicSpecialUnitary_sharedPlaquetteInfluence_eq_sparseActiveTVInfluence_current
    (n N : ℕ) [NeZero n]
    (hn : 3 <= n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 <= beta)
    (target source : PeriodicHypercubicEdge n) :
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta hBeta target source =
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source := by
  classical
  by_cases hEq : target = source
  · subst source
    rw [specialUnitaryCompactOrientedSharedPlaquetteInfluence_diagonal_zero]
    exact
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence_diagonal_zero
        n beta target |>.symm
  · by_cases hActive : source ∈ periodicHypercubicActiveNeighbors n target
    · have hConcreteCard :
          (periodicHypercubicSharedPlaquettes n target source).card = 1 :=
        periodicHypercubic_sharedPlaquettes_card_eq_one_of_active_current
          n hn target source hActive
      have hGenericCard :
          (((specialUnitaryContinuousCompactOrientedDensityRatioSystem
              (periodicHypercubicFiniteOrientedGeometry n)
              N hN beta hBeta).base.sharedPlaquettes
              target source).card : ℝ) = 1 := by
        change
          (((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta hBeta).base.sharedPlaquettes
              target source).card : ℝ) = 1
        rw [periodicHypercubicSpecialUnitary_sharedPlaquettes_eq_current
          n N hN beta hBeta target source,
          hConcreteCard]
        norm_num
      unfold specialUnitaryCompactOrientedSharedPlaquetteInfluence
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        periodicHypercubicSpecialUnitaryActiveTVMajorant
        compactHaarOscillationInfluence
        HaarLikelihoodRatioInfluence.coefficient
      simp only [hEq, if_false, hActive, if_true]
      rw [hGenericCard]
      ring_nf
    · have hNe : source ≠ target := Ne.symm hEq
      have hShared :=
        periodicHypercubicSpecialUnitary_sharedPlaquettes_eq_empty_of_inactive
          n N hN beta hBeta target source hActive hNe
      have hGenericCard :
          (((specialUnitaryContinuousCompactOrientedDensityRatioSystem
              (periodicHypercubicFiniteOrientedGeometry n)
              N hN beta hBeta).base.sharedPlaquettes
              target source).card : ℝ) = 0 := by
        change
          (((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta hBeta).base.sharedPlaquettes
              target source).card : ℝ) = 0
        rw [hShared]
        simp
      unfold specialUnitaryCompactOrientedSharedPlaquetteInfluence
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        compactHaarOscillationInfluence
        HaarLikelihoodRatioInfluence.coefficient
      simp only [hEq, if_false, hActive]
      rw [hGenericCard]
      norm_num

/-- Under the explicit high-temperature row threshold, the actual periodic
compact `SU(N)` one-link laws instantiate the already-canonical generic
Dobrushin matrix carrier. -/
noncomputable def periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
    (n N : ℕ) [NeZero n]
    (hn : 3 <= n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 <= beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1) :
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  refine
    { influence := fun target source =>
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta hBeta target source
      influence_nonneg := ?_
      influence_diagonal_zero := ?_
      conditionalIntegral_difference_abs_le := ?_
      coefficient :=
        18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta
      coefficient_nonneg := ?_
      rowSum_le_coefficient := ?_
      coefficient_lt_one := hThreshold }
  · intro target source
    exact
      specialUnitaryCompactOrientedSharedPlaquetteInfluence_nonneg
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta hBeta target source
  · intro target
    exact
      specialUnitaryCompactOrientedSharedPlaquetteInfluence_diagonal_zero
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta hBeta target
  · intro target source A B hAgree phi hphi hphiBound
    simpa [C, periodicHypercubicSpecialUnitaryWilsonSystem] using
      (specialUnitaryContinuousCompactOriented_conditionalIntegral_difference_abs_le
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta hBeta A B target source hAgree phi hphi hphiBound)
  · exact mul_nonneg (by norm_num)
      (periodicHypercubicSpecialUnitaryActiveTVMajorant_nonneg beta hBeta)
  · intro target
    calc
      (∑ source : PeriodicHypercubicEdge n,
          specialUnitaryCompactOrientedSharedPlaquetteInfluence
            (periodicHypercubicFiniteOrientedGeometry n)
            N hN beta hBeta target source) =
        ∑ source : PeriodicHypercubicEdge n,
          periodicHypercubicSpecialUnitarySparseActiveTVInfluence
            n beta target source := by
          apply Finset.sum_congr rfl
          intro source _
          exact
            periodicHypercubicSpecialUnitary_sharedPlaquetteInfluence_eq_sparseActiveTVInfluence_current
              n N hn hN beta hBeta target source
      _ <= 18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta :=
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence_rowSum_le_eighteen
          n beta hBeta target

end

end MathlibAnalytic
end MGAP4D
