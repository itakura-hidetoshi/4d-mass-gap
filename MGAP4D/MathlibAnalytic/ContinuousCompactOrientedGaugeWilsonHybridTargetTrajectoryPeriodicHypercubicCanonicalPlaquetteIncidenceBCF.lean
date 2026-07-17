import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryOrientedPlaquetteComplementStapleBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceCompleteness
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The generic compact-system boundary edge is definitionally the physical
edge of the actual signed periodic boundary incidence. -/
@[simp]
theorem periodicHypercubicSpecialUnitaryWilsonSystem_boundary_edge
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (k : Fin 4) :
    ((periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).base.geometry.boundary p k).edge =
      (periodicHypercubicBoundaryStep n p k).edge := by
  rfl

/-- In a nondegenerate periodic box, every transverse-axis/two-side datum gives
an isolated target incidence in the actual periodic `SU(N)` Wilson geometry. -/
def periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (data : PeriodicHypercubicOtherAxis target.2 × Bool) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).IsolatedTargetPlaquetteIncidence target := by
  rcases target with ⟨x, mu⟩
  rcases data with ⟨⟨nu, hne⟩, otherSide⟩
  by_cases hlt : mu < nu
  · cases otherSide
    · apply ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.at0
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ false)
      all_goals
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe,
          periodicHypercubicPlaquetteFirstAxis,
          periodicHypercubicPlaquetteSecondAxis,
          hlt, hne,
          periodicHypercubicShift_ne_self n hn x nu,
          periodicHypercubicUnshift_ne_self n hn x nu]
    · apply ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.at2
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ true)
      all_goals
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe,
          periodicHypercubicPlaquetteFirstAxis,
          periodicHypercubicPlaquetteSecondAxis,
          hlt, hne,
          periodicHypercubicShift_ne_self n hn x nu,
          periodicHypercubicUnshift_ne_self n hn x nu]
  · cases otherSide
    · apply ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.at3
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ false)
      all_goals
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe,
          periodicHypercubicPlaquetteFirstAxis,
          periodicHypercubicPlaquetteSecondAxis,
          hlt, hne,
          periodicHypercubicShift_ne_self n hn x nu,
          periodicHypercubicUnshift_ne_self n hn x nu]
    · apply ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.at1
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ true)
      all_goals
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe,
          periodicHypercubicPlaquetteFirstAxis,
          periodicHypercubicPlaquetteSecondAxis,
          hlt, hne,
          periodicHypercubicShift_ne_self n hn x nu,
          periodicHypercubicUnshift_ne_self n hn x nu]

@[simp]
theorem periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence_plaquette
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (data : PeriodicHypercubicOtherAxis target.2 × Bool) :
    (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
      n N hn hN beta beta_nonneg target data).plaquette =
      periodicHypercubicIncidentPlaquette n target data.1 data.2 := by
  rcases target with ⟨x, mu⟩
  rcases data with ⟨⟨nu, hne⟩, otherSide⟩
  by_cases hlt : mu < nu <;> cases otherSide <;>
    simp [periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence,
      ContinuousCompactOrientedGaugeWilsonSystem.IsolatedTargetPlaquetteIncidence.plaquette,
      hlt]

/-- The canonical target-plaquette index has exactly six elements. -/
theorem periodicHypercubicCanonicalTargetPlaquetteIndex_card
    (n : ℕ)
    (target : PeriodicHypercubicEdge n) :
    Fintype.card (PeriodicHypercubicOtherAxis target.2 × Bool) = 6 := by
  rw [Fintype.card_prod, periodicHypercubicOtherAxis_card]
  native_decide

/-- The six canonical complements form a target-independent staple family. -/
theorem periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteStapleFamily_targetIndependent
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).targetIndependentStapleFamilyBCF target
      (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
        (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
          n N hn hN beta beta_nonneg target data).stapleContinuousMap) := by
  exact
    continuous_compact_oriented_isolatedTargetPlaquetteIncidence_stapleFamily_targetIndependent
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg)
      target
      (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
        n N hn hN beta beta_nonneg target)

/-- The six canonical periodic plaquettes have exactly the actual touching set
as their image. -/
theorem periodicHypercubicCanonicalTargetPlaquette_image_eq_touching
    (n : ℕ)
    [NeZero n]
    (target : PeriodicHypercubicEdge n) :
    Finset.univ.image
        (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
          periodicHypercubicIncidentPlaquette n target data.1 data.2) =
      periodicHypercubicTouchingPlaquettes n target := by
  rw [periodicHypercubicTouchingPlaquettes_eq_incidentPlaquettes]
  rfl

/-- The bounded continuous six-slot periodic target-plaquette observable. -/
def periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    BoundedContinuousFunction
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ℝ :=
  (periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta beta_nonneg).isolatedTargetPlaquetteObservableBCF target
      (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
        n N hn hN beta beta_nonneg target)

/-- After target insertion, the observable is the six-slot sum of actual signed
periodic `SU(N)` Wilson plaquette energies. -/
theorem periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF_replaceLink_apply
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (A : PeriodicHypercubicEdge n → SpecialUnitaryMatrixGroup N)
    (g : SpecialUnitaryMatrixGroup N) :
    periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF
        n N hn hN beta beta_nonneg target
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).base.replaceLink A target g) =
      ∑ data : PeriodicHypercubicOtherAxis target.2 × Bool,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).base.replaceLink A target g)
            (periodicHypercubicIncidentPlaquette
              n target data.1 data.2)) := by
  unfold periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF
  rw [continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_replaceLink_apply
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg)
    (specialUnitaryContinuousCompactOrientedGaugeWilsonSystem_plaquetteEnergy_inv
      (periodicHypercubicFiniteOrientedGeometry n)
      N hN beta beta_nonneg)
    target
    (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
      n N hn hN beta beta_nonneg target)
    A g]
  apply Finset.sum_congr rfl
  intro data _hdata
  rw [periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence_plaquette]
  rfl

end

end MathlibAnalytic
end MGAP4D
