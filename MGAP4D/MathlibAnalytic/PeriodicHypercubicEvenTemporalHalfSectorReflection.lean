import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedWilsonGibbsDensitySeparatedHalves
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsSectorFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The base time of a reflected time-containing plaquette is `-(t+1)`. -/
theorem periodicHypercubicEvenPlaquetteReflection_base_time_of_hasTimeDirection
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    (periodicHypercubicEvenPlaquetteReflection H p).1 0 =
      -(p.1 0 + 1) := by
  change periodicHypercubicEvenReflectedPlaquetteBase H p 0 =
    -(p.1 0 + 1)
  unfold periodicHypercubicEvenReflectedPlaquetteBase
  rw [if_pos htime]
  simp [periodicHypercubicUnshift, periodicHypercubicUnit,
    periodicHypercubicEvenTimeReflection]
  abel

/-- Recover a periodic time from its canonical natural residue. -/
theorem periodicHypercubicEvenTime_eq_natCast_of_val_eq
    (H k : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (hval : t.val = k) :
    t = (k : ZMod (PeriodicHypercubicEvenSideLength H)) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  calc
    t = ((t.val : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) :=
      (ZMod.natCast_zmod_val t).symm
    _ = (k : ZMod (PeriodicHypercubicEvenSideLength H)) := by
      rw [hval]

/-- Reflection of the temporal plaquette based at time `0` is based at the last
negative residue `2H+1`. -/
theorem periodicHypercubicEven_neg_add_one_val_of_val_eq_zero
    (H : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (hval : t.val = 0) :
    (-(t + 1)).val = 2 * H + 1 := by
  have ht : t = 0 := (ZMod.val_eq_zero t).mp hval
  subst t
  have hside : PeriodicHypercubicEvenSideLength H = (2 * H + 1).succ := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  change (-1 : ZMod (PeriodicHypercubicEvenSideLength H)).val = 2 * H + 1
  rw [hside]
  exact ZMod.val_neg_one (2 * H + 1)

/-- Reflection of the temporal plaquette based at the last positive residue
`H` is based at the antipodal fixed slice `H+1`. -/
theorem periodicHypercubicEven_neg_add_one_val_of_val_eq_H
    (H : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (hval : t.val = H) :
    (-(t + 1)).val = H + 1 := by
  have ht := periodicHypercubicEvenTime_eq_natCast_of_val_eq H H t hval
  rw [ht, ← Nat.cast_one, ← Nat.cast_add]
  rw [periodicHypercubicEven_neg_halfPeriod]
  have hlt : H + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  exact ZMod.val_natCast_of_lt hlt

/-- Reflection of the temporal plaquette based at the antipodal fixed slice
`H+1` is based at the last positive residue `H`. -/
theorem periodicHypercubicEven_neg_add_one_val_of_val_eq_half
    (H : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (hval : t.val = H + 1) :
    (-(t + 1)).val = H := by
  have ht :=
    periodicHypercubicEvenTime_eq_natCast_of_val_eq H (H + 1) t hval
  rw [ht]
  have hnat : H + (H + 1 + 1) = PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hcast :
      ((H + (H + 1 + 1) : ℕ) :
          ZMod (PeriodicHypercubicEvenSideLength H)) = 0 := by
    rw [hnat, ZMod.natCast_self]
  have hsum :
      ((H : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) +
          (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) + 1) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hcast
  have heq :
      -(((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) + 1) =
        ((H : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := by
    calc
      -(((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) + 1) =
          -(((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) + 1) +
            (((H : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) +
              (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) + 1)) := by
                rw [hsum]
                simp
      _ = ((H : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := by
        abel
  rw [heq]
  have hlt : H < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  exact ZMod.val_natCast_of_lt hlt

/-- Reflection of the temporal plaquette based at the last negative residue
`2H+1` is based at the primary fixed slice `0`. -/
theorem periodicHypercubicEven_neg_add_one_val_of_val_eq_last
    (H : ℕ) (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (hval : t.val = 2 * H + 1) :
    (-(t + 1)).val = 0 := by
  have ht :=
    periodicHypercubicEvenTime_eq_natCast_of_val_eq H (2 * H + 1) t hval
  rw [ht]
  have hnat : 2 * H + 1 + 1 = PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hcast :
      ((2 * H + 1 + 1 : ℕ) :
          ZMod (PeriodicHypercubicEvenSideLength H)) = 0 := by
    rw [hnat, ZMod.natCast_self]
  have hsum :
      (((2 * H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) + 1) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hcast
  rw [hsum]
  simp

/-- Reflection sends positive-boundary temporal plaquettes to the corresponding
negative-boundary temporal plaquettes. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_reflection
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p) :
    periodicHypercubicEvenNegativeBoundaryTemporalPlaquette
      (periodicHypercubicEvenPlaquetteReflection H p) := by
  refine ⟨(periodicHypercubicEvenPlaquetteReflection_hasTimeDirection H p).2 hp.1, ?_⟩
  rw [periodicHypercubicEvenPlaquetteReflection_base_time_of_hasTimeDirection
    H p hp.1]
  rcases hp.2 with hzero | hH
  · right
    exact periodicHypercubicEven_neg_add_one_val_of_val_eq_zero H (p.1 0) hzero
  · left
    exact periodicHypercubicEven_neg_add_one_val_of_val_eq_H H (p.1 0) hH

/-- Reflection sends negative-boundary temporal plaquettes to the corresponding
positive-boundary temporal plaquettes. -/
theorem periodicHypercubicEvenNegativeBoundaryTemporalPlaquette_reflection
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p) :
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
      (periodicHypercubicEvenPlaquetteReflection H p) := by
  refine ⟨(periodicHypercubicEvenPlaquetteReflection_hasTimeDirection H p).2 hp.1, ?_⟩
  rw [periodicHypercubicEvenPlaquetteReflection_base_time_of_hasTimeDirection
    H p hp.1]
  rcases hp.2 with hhalf | hlast
  · right
    exact periodicHypercubicEven_neg_add_one_val_of_val_eq_half H (p.1 0) hhalf
  · left
    exact periodicHypercubicEven_neg_add_one_val_of_val_eq_last H (p.1 0) hlast

/-- Plaquette reflection exchanges the positive and negative boundary-temporal
predicates. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_positiveBoundaryTemporal_iff_negativeBoundaryTemporal
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p := by
  constructor
  · intro hp
    have hreflected :=
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_reflection
        H (periodicHypercubicEvenPlaquetteReflection H p) hp
    rw [periodicHypercubicEvenPlaquetteReflection_involutive H p] at hreflected
    exact hreflected
  · exact periodicHypercubicEvenNegativeBoundaryTemporalPlaquette_reflection H p

/-- The reverse boundary-temporal predicate exchange. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteReflection_negativeBoundaryTemporal_iff_positiveBoundaryTemporal
    (H : ℕ) (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenNegativeBoundaryTemporalPlaquette
        (periodicHypercubicEvenPlaquetteReflection H p) ↔
      periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p := by
  constructor
  · intro hp
    have hreflected :=
      periodicHypercubicEvenNegativeBoundaryTemporalPlaquette_reflection
        H (periodicHypercubicEvenPlaquetteReflection H p) hp
    rw [periodicHypercubicEvenPlaquetteReflection_involutive H p] at hreflected
    exact hreflected
  · exact periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_reflection H p

/-- A restricted Wilson action is transported from predicate `P` to predicate
`Q` whenever plaquette reflection exchanges the predicates. -/
theorem periodicHypercubicEvenRestrictedWilsonAction_configurationReflection_exchange
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (P Q : PeriodicHypercubicEvenPlaquette H → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ p, P (periodicHypercubicEvenPlaquetteReflection H p) ↔ Q p)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      propositionIndicator (P p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            (periodicHypercubicEvenConfigurationReflection H A) p))) =
      ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator (Q p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
  classical
  calc
    (∑ p : PeriodicHypercubicEvenPlaquette H,
      propositionIndicator (P p)
        (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy
            (periodicHypercubicEvenConfigurationReflection H A) p))) =
      ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator (P p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPlaquetteReflection H p))) := by
                apply Finset.sum_congr rfl
                intro p _hp
                rw [periodicHypercubicEvenWilsonPlaquetteEnergy_configurationReflection]
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator
          (P (periodicHypercubicEvenPlaquetteReflection H
            (periodicHypercubicEvenPlaquetteReflection H p)))
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A
              (periodicHypercubicEvenPlaquetteReflection H p))) := by
              apply Finset.sum_congr rfl
              intro p _hp
              rw [periodicHypercubicEvenPlaquetteReflection_involutive H p]
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator
          (P (periodicHypercubicEvenPlaquetteReflection H p))
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
              exact periodicHypercubicEvenPlaquette_sum_reflection H
                (fun p : PeriodicHypercubicEvenPlaquette H =>
                  propositionIndicator
                    (P (periodicHypercubicEvenPlaquetteReflection H p))
                    (specialUnitaryWilsonPlaquetteEnergy N
                      (periodicHypercubicPlaquetteHolonomy A p)))
    _ = ∑ p : PeriodicHypercubicEvenPlaquette H,
        propositionIndicator (Q p)
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p)) := by
              apply Finset.sum_congr rfl
              intro p _hp
              rw [hPQ p]

/-- Reflection exchanges the positive-boundary temporal Wilson action with the
negative-boundary temporal Wilson action. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_configurationReflection
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N A := by
  classical
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction
  unfold periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction
  simpa only using
    periodicHypercubicEvenRestrictedWilsonAction_configurationReflection_exchange
      H N periodicHypercubicEvenPositiveBoundaryTemporalPlaquette
      periodicHypercubicEvenNegativeBoundaryTemporalPlaquette
      (periodicHypercubicEvenPlaquetteReflection_positiveBoundaryTemporal_iff_negativeBoundaryTemporal H) A

/-- Reflection exchanges the negative-boundary temporal Wilson action with the
positive-boundary temporal Wilson action. -/
theorem periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction_configurationReflection
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction H N
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction H N A := by
  rw [← periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_configurationReflection
    H N (periodicHypercubicEvenConfigurationReflection H A)]
  rw [periodicHypercubicEvenConfigurationReflection_involutive H A]

/-- Reflection exchanges the two boundary-temporal Boltzmann weights. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_configurationReflection
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
        H N beta A := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  unfold periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonAction_configurationReflection]

/-- Reflection exchanges the reverse boundary-temporal Boltzmann weight. -/
theorem periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight_configurationReflection
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
        H N beta A := by
  unfold periodicHypercubicEvenNegativeBoundaryTemporalWilsonBoltzmannWeight
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight
  rw [periodicHypercubicEvenNegativeBoundaryTemporalWilsonAction_configurationReflection]

/-- Reflection exchanges the completed positive and negative Wilson half
amplitudes. -/
theorem periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_configurationReflection
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude
        H N beta A := by
  unfold periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_configurationReflection]
  rw [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoltzmannWeight_configurationReflection]

/-- Reflection exchanges the completed negative and positive Wilson half
amplitudes. -/
theorem periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude_configurationReflection
    (H N : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCompletedNegativeWilsonBoltzmannAmplitude H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude
        H N beta A := by
  rw [← periodicHypercubicEvenCompletedPositiveWilsonBoltzmannAmplitude_configurationReflection
    H N beta (periodicHypercubicEvenConfigurationReflection H A)]
  rw [periodicHypercubicEvenConfigurationReflection_involutive H A]

end

end MathlibAnalytic
end MGAP4D
