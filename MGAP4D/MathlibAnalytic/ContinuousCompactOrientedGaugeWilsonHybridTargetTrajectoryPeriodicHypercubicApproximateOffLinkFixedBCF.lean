import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicOffLinkMeasurableIntersectionBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

/-- Unit Gibbs-vacuum orthogonal vectors that become uniformly approximately
fixed by every physical-link conditional expectation.  Since each projection
has the corresponding off-link `lpMeas` space as its range, this is the exact
finite-volume approximate off-link measurability obstruction. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
      ∃ f : Lp ℝ 2 C.gibbsMeasure,
        f ∈ C.VacuumOrthogonalL2 ∧
          ‖f‖ = 1 ∧
            ∀ target : C.base.geometry.Edge,
              ‖f - C.singleLinkHeatBathProjectionL2 target f‖ < ε

/-- Arbitrarily small Hamiltonian energy is equivalent to simultaneous
approximate fixedness under every local off-link conditional expectation.
The forward direction bounds every local defect by the total sum of squares.
The reverse direction uses the finite number of physical links and the scale
`sqrt (ε / (|E| + 1))`. -/
theorem continuous_compact_oriented_periodicApproximateOffLinkFixed_approximateZeroEnergy_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalUnitApproximateZeroEnergy ↔
      C.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2 := by
  classical
  constructor
  · intro hApproximateEnergy ε hε
    have hεSq : 0 < ε ^ 2 := by positivity
    rcases hApproximateEnergy (ε ^ 2) hεSq with
      ⟨f, hfOrth, hfNorm, hfEnergy⟩
    refine ⟨f, hfOrth, hfNorm, ?_⟩
    rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm] at hfEnergy
    intro target
    have hTermLe :
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 ≤
          ∑ edge : C.base.geometry.Edge,
            ‖C.singleLinkHeatBathFluctuationL2 edge f‖ ^ 2 := by
      exact Finset.single_le_sum
        (fun edge _ =>
          sq_nonneg ‖C.singleLinkHeatBathFluctuationL2 edge f‖)
        (Finset.mem_univ target)
    have hTermLt :
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 < ε ^ 2 :=
      lt_of_le_of_lt hTermLe hfEnergy
    have hNormLt :
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ < ε := by
      nlinarith [norm_nonneg
        (C.singleLinkHeatBathFluctuationL2 target f)]
    simpa [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] using
      hNormLt
  · intro hApproximateFixed ε hε
    let N : ℝ := Fintype.card C.base.geometry.Edge
    have hNNonneg : 0 ≤ N := by
      dsimp [N]
      positivity
    have hNPlusPos : 0 < N + 1 := by
      linarith
    have hQuotPos : 0 < ε / (N + 1) :=
      div_pos hε hNPlusPos
    let δ : ℝ := Real.sqrt (ε / (N + 1))
    have hδPos : 0 < δ := by
      dsimp [δ]
      exact Real.sqrt_pos.2 hQuotPos
    have hδSq : δ ^ 2 = ε / (N + 1) := by
      dsimp [δ]
      exact Real.sq_sqrt (le_of_lt hQuotPos)
    rcases hApproximateFixed δ hδPos with
      ⟨f, hfOrth, hfNorm, hfFixed⟩
    refine ⟨f, hfOrth, hfNorm, ?_⟩
    rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
    have hEach :
        ∀ target : C.base.geometry.Edge,
          ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 ≤
            ε / (N + 1) := by
      intro target
      have hNormLt :
          ‖C.singleLinkHeatBathFluctuationL2 target f‖ < δ := by
        simpa [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] using
          hfFixed target
      have hSqLt :
          ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 < δ ^ 2 := by
        nlinarith [norm_nonneg
          (C.singleLinkHeatBathFluctuationL2 target f)]
      exact le_of_lt (by simpa [hδSq] using hSqLt)
    calc
      (∑ target : C.base.geometry.Edge,
          ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2) ≤
          ∑ _target : C.base.geometry.Edge, ε / (N + 1) := by
        exact Finset.sum_le_sum fun target _ => hEach target
      _ = N * (ε / (N + 1)) := by
        simp [N]
      _ < ε := by
        have hStep :
            N * (ε / (N + 1)) <
              (N + 1) * (ε / (N + 1)) :=
          mul_lt_mul_of_pos_right (lt_add_one N) hQuotPos
        have hCancel :
            (N + 1) * (ε / (N + 1)) = ε := by
          field_simp [ne_of_gt hNPlusPos]
        rw [hCancel] at hStep
        exact hStep

/-- Actual side-three periodic `SU(2)` approximate zero-energy vectors are
exactly unit vacuum-orthogonal vectors uniformly approximately fixed by every
physical-link off-link conditional expectation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_approximateZeroEnergy_iff_approximateOffLinkFixed :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateZeroEnergy ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2 := by
  exact
    continuous_compact_oriented_periodicApproximateOffLinkFixed_approximateZeroEnergy_iff
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem

/-- The actual Rayleigh infimum vanishes exactly when unit vectors become
simultaneously approximately off-link measurable at every physical link. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_eq_zero_iff_approximateOffLinkFixed :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_eq_zero_iff_approximateZeroEnergy.trans
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_approximateZeroEnergy_iff_approximateOffLinkFixed

/-- Strict positivity of the actual finite-volume lower edge is exactly the
absence of uniformly approximate common off-link fixed unit vectors.  This is
a characterization, not a proof of the absence statement. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_not_approximateOffLinkFixed :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2 := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_not_approximateZeroEnergy.trans
      (not_congr
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_approximateZeroEnergy_iff_approximateOffLinkFixed)

/-- Compact proof-facing package for the actual approximate off-link fixed-space
frontier. -/
def periodicHypercubicThreeSpecialUnitaryTwoApproximateOffLinkFixedFrontierReceipt : Prop :=
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateZeroEnergy ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2) ∧
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum = 0 ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2) ∧
  (0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
    ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2)

/-- The remaining actual positive-gap problem is now expressed as a quantitative
separation problem for the finite family of off-link measurable subspaces.
Exact intersection triviality alone does not supply this uniform separation. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoApproximateOffLinkFixedFrontierReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoApproximateOffLinkFixedFrontierReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_approximateZeroEnergy_iff_approximateOffLinkFixed,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_eq_zero_iff_approximateOffLinkFixed,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_not_approximateOffLinkFixed⟩

end

end MathlibAnalytic
end MGAP4D
