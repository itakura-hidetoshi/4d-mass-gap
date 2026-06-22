import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingTimeClassification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingWilsonActionSpatialTemporal
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A time-containing plaquette adjacent to a reflection-fixed slice from the
strict-positive side.  Its base time is either the primary fixed slice `0` or
the last positive slice `H`. -/
def periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
    ((p.1 0).val = 0 ∨ (p.1 0).val = H)

/-- A time-containing plaquette adjacent to a reflection-fixed slice from the
strict-negative side.  Its base time is either the antipodal fixed slice
`H+1` or the last negative slice `2H+1`. -/
def periodicHypercubicEvenNegativeBoundaryTemporalPlaquette
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) : Prop :=
  periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
    ((p.1 0).val = H + 1 ∨ (p.1 0).val = 2 * H + 1)

/-- The temporal crossing sector is exactly the disjoint union of the
positive-boundary-adjacent and negative-boundary-adjacent sectors. -/
theorem periodicHypercubicEvenTemporalCrossingPlaquette_iff_positiveBoundary_or_negativeBoundary
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenTemporalCrossingPlaquette p ↔
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p ∨
        periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p := by
  rw [periodicHypercubicEvenTemporalCrossingPlaquette_iff_baseTime_val]
  unfold periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
  unfold periodicHypercubicEvenNegativeBoundaryTemporalPlaquette
  tauto

/-- The two boundary-adjacent temporal sectors are disjoint. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_not_negativeBoundary
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    ¬ periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p := by
  rintro ⟨_htime, hn⟩
  rcases hp.2 with hp0 | hpH <;>
    rcases hn with hnH1 | hnLast <;> omega

/-- Positive-boundary-adjacent temporal contribution to the Wilson action. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- Negative-boundary-adjacent temporal contribution to the Wilson action. -/
noncomputable def periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (PeriodicHypercubicEvenPlaquette H)),
    propositionIndicator
      (periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p)
      (specialUnitaryWilsonPlaquetteEnergy N
        (periodicHypercubicPlaquetteHolonomy A p))

/-- The time-containing crossing action is exactly the sum of its two
boundary-adjacent half-sector actions. -/
theorem periodicHypercubicEvenTemporalCrossingWilsonAction_eq_positiveBoundary_add_negativeBoundary
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenTemporalCrossingWilsonAction H N A =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A +
        periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenTemporalCrossingWilsonAction
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  unfold periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpositive :
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p
  · have hnotnegative :=
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_not_negativeBoundary
        p hpositive
    have htemporal : periodicHypercubicEvenTemporalCrossingPlaquette p :=
      (periodicHypercubicEvenTemporalCrossingPlaquette_iff_positiveBoundary_or_negativeBoundary
        p).2 (Or.inl hpositive)
    simp [propositionIndicator, hpositive, hnotnegative, htemporal]
  · by_cases hnegative :
      periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p
    · have htemporal : periodicHypercubicEvenTemporalCrossingPlaquette p :=
        (periodicHypercubicEvenTemporalCrossingPlaquette_iff_positiveBoundary_or_negativeBoundary
          p).2 (Or.inr hnegative)
      simp [propositionIndicator, hpositive, hnegative, htemporal]
    · have hnottemporal :
        ¬ periodicHypercubicEvenTemporalCrossingPlaquette p := by
        intro htemporal
        rcases
          (periodicHypercubicEvenTemporalCrossingPlaquette_iff_positiveBoundary_or_negativeBoundary
            p).1 htemporal with hp | hn
        · exact hpositive hp
        · exact hnegative hn
      simp [propositionIndicator, hpositive, hnegative, hnottemporal]

/-- Positive-boundary-adjacent temporal Boltzmann weight. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp
    (-beta * periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A)

/-- Negative-boundary-adjacent temporal Boltzmann weight. -/
noncomputable def periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp
    (-beta * periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N A)

/-- The temporal crossing Boltzmann weight factors into the two
boundary-adjacent half-sector weights. -/
theorem periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight_eq_positiveBoundary_mul_negativeBoundary
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight H N beta A =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
          H N beta A *
        periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
          H N beta A := by
  unfold periodicHypercubicEvenTemporalCrossingWilsonBoltzmannWeight
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  unfold periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
  rw [periodicHypercubicEvenTemporalCrossingWilsonAction_eq_positiveBoundary_add_negativeBoundary]
  rw [show -beta *
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A +
        periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N A) =
      (-beta * periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A) +
        (-beta * periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N A) by ring]
  rw [Real.exp_add]

end

end MathlibAnalytic
end MGAP4D
