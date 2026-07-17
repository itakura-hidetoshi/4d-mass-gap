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

/-- In a nondegenerate periodic box, every transverse-axis/two-side datum gives
an isolated target incidence in the actual periodic `SU(N)` Wilson geometry.
The four branches retain the genuine cyclic boundary position and traversal
orientation of the target physical link. -/
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
    · apply .at0
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ false)
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 0).edge = (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 1).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 2).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt,
          periodicHypercubicShift_ne_self n hn x nu]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 3).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
    · apply .at2
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ true)
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 0).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt,
          periodicHypercubicUnshift_ne_self n hn x nu]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 1).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 2).edge = (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 3).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
  · cases otherSide
    · apply .at3
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ false)
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 0).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 1).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt,
          periodicHypercubicShift_ne_self n hn x nu]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 2).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ false) 3).edge = (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt]
    · apply .at1
        (periodicHypercubicIncidentPlaquette n (x, mu) ⟨nu, hne⟩ true)
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 0).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 1).edge = (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 2).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt, hne]
      · change
          (periodicHypercubicBoundaryStep n
            (periodicHypercubicIncidentPlaquette n
              (x, mu) ⟨nu, hne⟩ true) 3).edge ≠ (x, mu)
        simp [periodicHypercubicIncidentPlaquette,
          periodicHypercubicAxisPairOfNe, hlt,
          periodicHypercubicUnshift_ne_self n hn x nu]

/-- The plaquette retained by the canonical isolated incidence is exactly the
previously constructed periodic incident plaquette. -/
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

/-- The canonical periodic target-plaquette index has exactly six elements:
three transverse coordinate axes and two sides. -/
theorem periodicHypercubicCanonicalTargetPlaquetteIndex_card
    (n : ℕ)
    (target : PeriodicHypercubicEdge n) :
    Fintype.card (PeriodicHypercubicOtherAxis target.2 × Bool) = 6 := by
  rw [Fintype.card_prod, periodicHypercubicOtherAxis_card]
  native_decide

/-- The six canonical periodic complements form a valid target-independent
multi-staple family. -/
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

/-- The plaquette image of the six canonical isolated incidences is exactly the
actual finite set of periodic coordinate plaquettes touching the target link. -/
theorem periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence_image_eq_touching
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    Finset.univ.image
        (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
          (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
            n N hn hN beta beta_nonneg target data).plaquette) =
      periodicHypercubicTouchingPlaquettes n target := by
  classical
  rw [periodicHypercubicTouchingPlaquettes_eq_incidentPlaquettes]
  unfold periodicHypercubicIncidentPlaquettes
  simp only [periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence_plaquette]

/-- The actual bounded continuous observable obtained from all six canonical
periodic target-incident plaquette complements. -/
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

/-- After inserting the target value, the canonical periodic observable is
exactly the six-slot sum of the actual signed periodic Wilson plaquette
energies. -/
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
  simpa [periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF,
    periodicHypercubicSpecialUnitaryWilsonSystem,
    specialUnitaryContinuousCompactOrientedGaugeWilsonSystem,
    specialUnitaryCompactOrientedGaugeWilsonSystem,
    periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence_plaquette] using
    (continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_replaceLink_apply
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg)
      (specialUnitaryContinuousCompactOrientedGaugeWilsonSystem_plaquetteEnergy_inv
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg)
      target
      (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
        n N hn hN beta beta_nonneg target)
      A g)

/-- Exact endpoint oscillation margin for the six canonical periodic Wilson
plaquette complements. -/
theorem periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF_oscillationMargin_eq
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (z :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ×
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridTargetTrajectoryEndpointInsertionProfileOscillationMarginBCF
        target
        (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF
          n N hn hN beta beta_nonneg target)
        z =
      abs
        (multiRightTranslateSumOscillationBCF
            (periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).plaquetteEnergyBCF
            (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
              (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
                n N hn hN beta beta_nonneg target data).stapleValue
                ((periodicHypercubicSpecialUnitaryWilsonSystem
                  n N hN beta beta_nonneg).independentPairHybridConfiguration
                    z.1 z.2 0)) -
          multiRightTranslateSumOscillationBCF
            (periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).plaquetteEnergyBCF
            (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
              (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
                n N hn hN beta beta_nonneg target data).stapleValue
                ((periodicHypercubicSpecialUnitaryWilsonSystem
                  n N hN beta beta_nonneg).independentPairHybridConfiguration
                    z.1 z.2
                    (Fintype.card (PeriodicHypercubicEdge n))))) := by
  exact
    continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_oscillationMargin_eq
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg)
      target
      (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
        n N hn hN beta beta_nonneg target)
      z

/-- The coordinate-update witness for the canonical periodic target observable
is exactly inequality of the two endpoint six-staple oscillations. -/
theorem periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF_coordinateUpdateWitness_iff
    (n N : ℕ)
    [NeZero n]
    (hn : 2 ≤ n)
    (hN : 0 < N)
    [Nontrivial (SpecialUnitaryMatrixGroup N)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n)
    (z :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration ×
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.Configuration) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target
        (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteObservableBCF
          n N hn hN beta beta_nonneg target)
        z ↔
      multiRightTranslateSumOscillationBCF
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).plaquetteEnergyBCF
          (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
            (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
              n N hn hN beta beta_nonneg target data).stapleValue
              ((periodicHypercubicSpecialUnitaryWilsonSystem
                n N hN beta beta_nonneg).independentPairHybridConfiguration
                  z.1 z.2 0)) ≠
        multiRightTranslateSumOscillationBCF
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).plaquetteEnergyBCF
          (fun data : PeriodicHypercubicOtherAxis target.2 × Bool =>
            (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
              n N hn hN beta beta_nonneg target data).stapleValue
              ((periodicHypercubicSpecialUnitaryWilsonSystem
                n N hN beta beta_nonneg).independentPairHybridConfiguration
                  z.1 z.2
                  (Fintype.card (PeriodicHypercubicEdge n))) := by
  exact
    continuous_compact_oriented_isolatedTargetPlaquetteObservableBCF_coordinateUpdateWitness_iff
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg)
      target
      (periodicHypercubicSpecialUnitaryCanonicalTargetPlaquetteIncidence
        n N hn hN beta beta_nonneg target)
      z

end

end MathlibAnalytic
end MGAP4D
