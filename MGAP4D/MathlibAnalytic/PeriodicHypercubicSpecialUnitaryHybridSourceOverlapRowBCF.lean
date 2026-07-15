import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridSourceOverlapInfluenceBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The source-step overlap transport energy vanishes exactly on the diagonal:
when the source step is the target step, replacing the target coordinate erases
all dependence on the pre/post target value before the target conditional law is
compared. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_diagonal_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridSourceOverlapTransportEnergyBCF target target O = 0 := by
  apply le_antisymm
  · have hLe :=
      continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_compactHaarOscillationInfluence_of_endpointMap_oscillation
        C target target O 0 (by norm_num) (by
          intro z u v
          dsimp only
            [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridEndpointPairMap]
          rw [continuous_compact_oriented_independentPairHybridPostEndpointMap_eq_replaceLink_pre_rightTarget
            C target z]
          simp [CompactOrientedGaugeWilsonSystem.replaceLink])
    simpa [compactHaarOscillationInfluence,
      HaarLikelihoodRatioInfluence.coefficient] using hLe
  · exact
      continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_nonneg
        C target target O

/-- Sum of all source-indexed exact overlap transport energies into one fixed
target link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportRowEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∑ source : C.base.geometry.Edge,
    C.independentPairHybridSourceOverlapTransportEnergyBCF target source O

/-- The total source-overlap transport row energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridSourceOverlapTransportRowEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportRowEnergyBCF
  exact Finset.sum_nonneg fun source _ =>
    continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_nonneg
      C target source O

/-- The canonical compact-oriented `SU(N)` transport estimate holds for every
source, including the diagonal source where both the transport energy and the
explicit Dobrushin entry vanish exactly. -/
theorem specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_sharedPlaquetteInfluence_all
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : geometry.Edge)
    (O : BoundedContinuousFunction
      (specialUnitaryContinuousCompactOrientedDensityRatioSystem
        geometry N hN beta beta_nonneg).base.Configuration ℝ) :
    let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg
    C.independentPairHybridSourceOverlapTransportEnergyBCF target source O ≤
      (2 * ‖O‖) ^ 2 *
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          geometry N hN beta beta_nonneg target source := by
  classical
  dsimp only
  let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
    geometry N hN beta beta_nonneg
  letI : T2Space C.base.Gauge := by
    change T2Space (Matrix.specialUnitaryGroup (Fin N) ℂ)
    infer_instance
  by_cases hEq : target = source
  · subst source
    rw [continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_diagonal_zero
      C target O]
    rw [specialUnitaryCompactOrientedSharedPlaquetteInfluence_diagonal_zero
      geometry N hN beta beta_nonneg target]
    simp
  · simpa [C] using
      specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_sharedPlaquetteInfluence
        geometry N hN beta beta_nonneg target source hEq O

/-- Summing the all-source `SU(N)` estimate gives the exact explicit influence
row as the transport multiplier. -/
theorem specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportRowEnergyBCF_le_influence_row
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : geometry.Edge)
    (O : BoundedContinuousFunction
      (specialUnitaryContinuousCompactOrientedDensityRatioSystem
        geometry N hN beta beta_nonneg).base.Configuration ℝ) :
    let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg
    C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O ≤
      (2 * ‖O‖) ^ 2 *
        ∑ source : geometry.Edge,
          specialUnitaryCompactOrientedSharedPlaquetteInfluence
            geometry N hN beta beta_nonneg target source := by
  classical
  dsimp only
  let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
    geometry N hN beta beta_nonneg
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportRowEnergyBCF
  calc
    (∑ source : geometry.Edge,
      C.independentPairHybridSourceOverlapTransportEnergyBCF target source O) ≤
        ∑ source : geometry.Edge,
          (2 * ‖O‖) ^ 2 *
            specialUnitaryCompactOrientedSharedPlaquetteInfluence
              geometry N hN beta beta_nonneg target source := by
      apply Finset.sum_le_sum
      intro source _
      simpa [C] using
        specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportEnergyBCF_le_sharedPlaquetteInfluence_all
          geometry N hN beta beta_nonneg target source O
    _ = (2 * ‖O‖) ^ 2 *
        ∑ source : geometry.Edge,
          specialUnitaryCompactOrientedSharedPlaquetteInfluence
            geometry N hN beta beta_nonneg target source := by
      rw [Finset.mul_sum]

/-- A periodic source outside the physical active-neighbor support contributes
exactly zero overlap transport energy.  The diagonal case is handled by the
exact diagonal theorem; the off-diagonal case follows from the zero explicit
influence entry. -/
theorem periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportEnergyBCF_eq_zero_of_not_active
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (hNotActive : source ∉ periodicHypercubicActiveNeighbors n target)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportEnergyBCF
        target source O = 0 := by
  classical
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg
  letI : T2Space C.base.Gauge := by
    change T2Space (Matrix.specialUnitaryGroup (Fin N) ℂ)
    infer_instance
  by_cases hEq : target = source
  · subst source
    simpa [C] using
      continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_diagonal_zero
        C target O
  · have hLe :=
      periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportEnergyBCF_le_influence
        n N hN beta beta_nonneg target source hEq O
    have hInfluenceZero :=
      periodicHypercubicSpecialUnitary_influence_eq_zero_of_not_active
        n N hN beta beta_nonneg target source hNotActive
    apply le_antisymm
    · simpa [hInfluenceZero] using hLe
    · exact
        continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_nonneg
          C target source O

/-- The periodic total source-overlap transport row is supported exactly inside
the finite physical active-neighbor set. -/
theorem periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportRowEnergyBCF_eq_sum_active
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportRowEnergyBCF
        target O =
      ∑ source ∈ periodicHypercubicActiveNeighbors n target,
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportEnergyBCF
            target source O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportRowEnergyBCF
  symm
  apply Finset.sum_subset
    (Finset.subset_univ (periodicHypercubicActiveNeighbors n target))
  intro source _ hNotActive
  exact
    periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportEnergyBCF_eq_zero_of_not_active
      n N hN beta beta_nonneg target source hNotActive O

/-- The periodic compact-Haar `SU(N)` source-overlap transport row has the
volume-uniform multiplier `18 * eta_beta`. -/
theorem periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportRowEnergyBCF_le_eighteen_mul_eta
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportRowEnergyBCF
        target O ≤
      (2 * ‖O‖) ^ 2 *
        (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta) := by
  calc
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportRowEnergyBCF
        target O ≤
      (2 * ‖O‖) ^ 2 *
        ∑ source : PeriodicHypercubicEdge n,
          specialUnitaryCompactOrientedSharedPlaquetteInfluence
            (periodicHypercubicFiniteOrientedGeometry n)
            N hN beta beta_nonneg target source := by
      simpa [periodicHypercubicSpecialUnitaryWilsonSystem] using
        specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportRowEnergyBCF_le_influence_row
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg target O
    _ ≤ (2 * ‖O‖) ^ 2 *
        (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta) := by
      exact mul_le_mul_of_nonneg_left
        (periodicHypercubicSpecialUnitary_influence_rowSum_le
          n N hn hN beta beta_nonneg target)
        (sq_nonneg (2 * ‖O‖))

/-- In the explicit small-coupling region, the full periodic source-overlap
transport row admits a nonnegative multiplier strictly below one. -/
theorem periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportRowEnergyBCF_exists_strict_contraction_factor
    (n N : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (target : PeriodicHypercubicEdge n)
    (O : BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ) :
    ∃ rho : ℝ,
      0 ≤ rho ∧ rho < 1 ∧
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).independentPairHybridSourceOverlapTransportRowEnergyBCF
            target O ≤ (2 * ‖O‖) ^ 2 * rho := by
  refine ⟨18 * periodicHypercubicSpecialUnitaryDobrushinEta beta, ?_, ?_, ?_⟩
  · apply mul_nonneg
    · norm_num
    · unfold periodicHypercubicSpecialUnitaryDobrushinEta
      apply compactHaarOscillationInfluence_nonneg
      positivity
  · exact periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_beta_lt
      beta hBetaLt
  · exact
      periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportRowEnergyBCF_le_eighteen_mul_eta
        n N hn hN beta beta_nonneg target O

end

end MathlibAnalytic
end MGAP4D
