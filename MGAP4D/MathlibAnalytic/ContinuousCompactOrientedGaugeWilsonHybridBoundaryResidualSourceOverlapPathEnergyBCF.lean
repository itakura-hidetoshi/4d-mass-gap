import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridBoundaryResidualSourcePathBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHybridSourceOverlapRowBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Sum of target-link overlap transport energies over the canonical source links
strictly before `target`.  This is the energy budget corresponding to the exact
left telescoping path constructed in the preceding layer. -/
def ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∑ source : C.base.geometry.Edge,
    if (C.canonicalEdgeOrder source).val <
        (C.canonicalEdgeOrder target).val then
      C.independentPairHybridSourceOverlapTransportEnergyBCF target source O
    else 0

/-- Sum of target-link overlap transport energies over the canonical source links
strictly after `target`.  This is the energy budget corresponding to the exact
right telescoping path constructed in the preceding layer. -/
def ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualRightSourceOverlapPathEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  ∑ source : C.base.geometry.Edge,
    if (C.canonicalEdgeOrder target).val <
        (C.canonicalEdgeOrder source).val then
      C.independentPairHybridSourceOverlapTransportEnergyBCF target source O
    else 0

/-- The combined off-target source-overlap energy budget along both residual
paths.  The target source itself is deliberately omitted. -/
def ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualSourceOverlapPathEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  C.hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF target O +
    C.hybridBoundaryResidualRightSourceOverlapPathEnergyBCF target O

/-- The left source-overlap path energy is nonnegative. -/
theorem continuous_compact_oriented_hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF target O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF
  apply Finset.sum_nonneg
  intro source _
  split_ifs
  · exact
      continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_nonneg
        C target source O
  · exact le_rfl

/-- The right source-overlap path energy is nonnegative. -/
theorem continuous_compact_oriented_hybridBoundaryResidualRightSourceOverlapPathEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.hybridBoundaryResidualRightSourceOverlapPathEnergyBCF target O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualRightSourceOverlapPathEnergyBCF
  apply Finset.sum_nonneg
  intro source _
  split_ifs
  · exact
      continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_nonneg
        C target source O
  · exact le_rfl

/-- Before using the diagonal-zero theorem, the full source-overlap row splits
exactly into the left path, the target diagonal term, and the right path. -/
theorem continuous_compact_oriented_hybridBoundaryResidualLeft_add_diagonal_add_right_eq_sourceOverlapRow
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF target O +
        C.independentPairHybridSourceOverlapTransportEnergyBCF target target O +
      C.hybridBoundaryResidualRightSourceOverlapPathEnergyBCF target O =
        C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O := by
  classical
  have hDiagonal :
      C.independentPairHybridSourceOverlapTransportEnergyBCF target target O =
        ∑ source : C.base.geometry.Edge,
          if source = target then
            C.independentPairHybridSourceOverlapTransportEnergyBCF target source O
          else 0 := by
    simp
  rw [hDiagonal]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualRightSourceOverlapPathEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridSourceOverlapTransportRowEnergyBCF
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro source _
  let sourceRank := (C.canonicalEdgeOrder source).val
  let targetRank := (C.canonicalEdgeOrder target).val
  by_cases hLeft : sourceRank < targetRank
  · have hRight : ¬ targetRank < sourceRank := by omega
    have hNe : source ≠ target := by
      intro hEq
      subst source
      exact (Nat.lt_irrefl targetRank) hLeft
    simp [sourceRank, targetRank, hLeft, hRight, hNe]
  · by_cases hRight : targetRank < sourceRank
    · have hNe : source ≠ target := by
        intro hEq
        subst source
        exact (Nat.lt_irrefl targetRank) hRight
      simp [sourceRank, targetRank, hLeft, hRight, hNe]
    · have hRank : sourceRank = targetRank := by omega
      have hFin : C.canonicalEdgeOrder source = C.canonicalEdgeOrder target := by
        apply Fin.ext
        exact hRank
      have hEq : source = target := C.canonicalEdgeOrder.injective hFin
      subst source
      simp [sourceRank, targetRank]

/-- Because the target-source overlap transport energy is exactly zero, the two
canonical off-target residual paths exhaust the full source-overlap row energy. -/
theorem continuous_compact_oriented_hybridBoundaryResidualSourceOverlapPathEnergyBCF_eq_row
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O =
      C.independentPairHybridSourceOverlapTransportRowEnergyBCF target O := by
  rw [ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualSourceOverlapPathEnergyBCF]
  have hSplit :=
    continuous_compact_oriented_hybridBoundaryResidualLeft_add_diagonal_add_right_eq_sourceOverlapRow
      C target O
  rw [continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_diagonal_zero
    C target O] at hSplit
  simpa using hSplit

/-- The combined residual source-overlap path energy is nonnegative. -/
theorem continuous_compact_oriented_hybridBoundaryResidualSourceOverlapPathEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 ≤ C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.hybridBoundaryResidualSourceOverlapPathEnergyBCF
  exact add_nonneg
    (continuous_compact_oriented_hybridBoundaryResidualLeftSourceOverlapPathEnergyBCF_nonneg
      C target O)
    (continuous_compact_oriented_hybridBoundaryResidualRightSourceOverlapPathEnergyBCF_nonneg
      C target O)

/-- For the actual compact-oriented `SU(N)` system, the canonical residual path
energy inherits the exact all-source Dobrushin influence-row estimate. -/
theorem specialUnitaryContinuousCompactOriented_hybridBoundaryResidualSourceOverlapPathEnergyBCF_le_influence_row
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
    C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O ≤
      (2 * ‖O‖) ^ 2 *
        ∑ source : geometry.Edge,
          specialUnitaryCompactOrientedSharedPlaquetteInfluence
            geometry N hN beta beta_nonneg target source := by
  dsimp only
  let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
    geometry N hN beta beta_nonneg
  letI : T2Space C.base.Gauge := by
    change T2Space (Matrix.specialUnitaryGroup (Fin N) ℂ)
    infer_instance
  rw [continuous_compact_oriented_hybridBoundaryResidualSourceOverlapPathEnergyBCF_eq_row
    C target O]
  simpa [C] using
    specialUnitaryContinuousCompactOriented_independentPairHybridSourceOverlapTransportRowEnergyBCF_le_influence_row
      geometry N hN beta beta_nonneg target O

/-- On the periodic four-dimensional `SU(N)` system, the complete canonical
residual path energy has the same volume-uniform `18 * eta_beta` multiplier as
the source-overlap row. -/
theorem periodicHypercubicSpecialUnitary_hybridBoundaryResidualSourceOverlapPathEnergyBCF_le_eighteen_mul_eta
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
      n N hN beta beta_nonneg).hybridBoundaryResidualSourceOverlapPathEnergyBCF
        target O ≤
      (2 * ‖O‖) ^ 2 *
        (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg
  letI : T2Space C.base.Gauge := by
    change T2Space (Matrix.specialUnitaryGroup (Fin N) ℂ)
    infer_instance
  rw [continuous_compact_oriented_hybridBoundaryResidualSourceOverlapPathEnergyBCF_eq_row
    C target O]
  simpa [C] using
    periodicHypercubicSpecialUnitary_independentPairHybridSourceOverlapTransportRowEnergyBCF_le_eighteen_mul_eta
      n N hn hN beta beta_nonneg target O

end

end MathlibAnalytic
end MGAP4D
