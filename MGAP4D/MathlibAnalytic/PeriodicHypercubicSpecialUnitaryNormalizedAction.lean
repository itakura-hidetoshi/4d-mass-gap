import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryPhysicalEmbedding
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The exact extended-nonnegative plaquette volume `6 * L^4`. -/
def periodicHypercubicOrientedPlaquetteVolume
    (sideLength : ℕ) : ENNReal :=
  ((6 * sideLength ^ 4 : ℕ) : ENNReal)

/-- Reciprocal normalization by the exact number of periodic plaquettes. -/
def periodicHypercubicOrientedReciprocalPlaquetteScale
    (sideLength : ℕ) : ENNReal :=
  (periodicHypercubicOrientedPlaquetteVolume sideLength)⁻¹

/-- Positive side length makes the periodic plaquette volume nonzero. -/
theorem periodicHypercubicOrientedPlaquetteVolume_ne_zero
    (sideLength : ℕ)
    (sideLength_pos : 0 < sideLength) :
    periodicHypercubicOrientedPlaquetteVolume sideLength ≠ 0 := by
  have hL : sideLength ≠ 0 := Nat.ne_of_gt sideLength_pos
  have hNat : 6 * sideLength ^ 4 ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (pow_ne_zero 4 hL)
  unfold periodicHypercubicOrientedPlaquetteVolume
  exact_mod_cast hNat

/-- The finite periodic plaquette volume is never infinite. -/
theorem periodicHypercubicOrientedPlaquetteVolume_ne_top
    (sideLength : ℕ) :
    periodicHypercubicOrientedPlaquetteVolume sideLength ≠ ⊤ := by
  unfold periodicHypercubicOrientedPlaquetteVolume
  exact ENNReal.natCast_ne_top _

/-- Reciprocal normalization cancels the exact periodic plaquette volume. -/
theorem periodicHypercubicOrientedReciprocalPlaquetteScale_mul_volume
    (sideLength : ℕ)
    (sideLength_pos : 0 < sideLength) :
    periodicHypercubicOrientedReciprocalPlaquetteScale sideLength *
        periodicHypercubicOrientedPlaquetteVolume sideLength = 1 := by
  exact ENNReal.inv_mul_cancel
    (periodicHypercubicOrientedPlaquetteVolume_ne_zero
      sideLength sideLength_pos)
    (periodicHypercubicOrientedPlaquetteVolume_ne_top sideLength)

/-- The unnormalized signed periodic `SU(N)` Wilson action is bounded by two
per plaquette. -/
theorem periodicHypercubicSpecialUnitaryWilsonActionObservable_le_volume_mul_two
    (sideLength N : ℕ)
    (sideLength_pos : 0 < sideLength)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEdge sideLength →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ENNReal.ofReal
        ((periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
          sideLength N sideLength_pos hN beta beta_nonneg).base.wilsonAction A) ≤
      periodicHypercubicOrientedPlaquetteVolume sideLength * 2 := by
  letI : NeZero sideLength := ⟨Nat.ne_of_gt sideLength_pos⟩
  rw [periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide_wilsonAction]
  have hOfRealSum :
      ENNReal.ofReal
          (∑ p : PeriodicHypercubicPlaquette sideLength,
            specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicPlaquetteHolonomy A p)) =
        ∑ p : PeriodicHypercubicPlaquette sideLength,
          ENNReal.ofReal
            (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicPlaquetteHolonomy A p)) := by
    simpa using
      (ENNReal.ofReal_sum_of_nonneg
        (s := Finset.univ)
        (f := fun p : PeriodicHypercubicPlaquette sideLength =>
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p))
        (fun p _hp =>
          specialUnitaryWilsonPlaquetteEnergy_nonneg hN
            (periodicHypercubicPlaquetteHolonomy A p)))
  rw [hOfRealSum]
  calc
    (∑ p : PeriodicHypercubicPlaquette sideLength,
        ENNReal.ofReal
          (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicPlaquetteHolonomy A p))) ≤
        ∑ _p : PeriodicHypercubicPlaquette sideLength, (2 : ENNReal) := by
      exact Finset.sum_le_sum fun p _hp => by
        simpa using
          ENNReal.ofReal_le_ofReal
            (specialUnitaryWilsonPlaquetteEnergy_le_two hN
              (periodicHypercubicPlaquetteHolonomy A p))
    _ = periodicHypercubicOrientedPlaquetteVolume sideLength * 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        periodicHypercubicPlaquette_card]
      rfl

/-- The reciprocal-volume normalized signed periodic `SU(N)` Wilson action is
uniformly bounded by the sharp universal constant two. -/
theorem periodicHypercubicSpecialUnitaryReciprocalActionObservable_le_two
    (sideLength N : ℕ)
    (sideLength_pos : 0 < sideLength)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEdge sideLength →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicOrientedReciprocalPlaquetteScale sideLength *
        ENNReal.ofReal
          ((periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
            sideLength N sideLength_pos hN beta beta_nonneg).base.wilsonAction A) ≤
      2 := by
  calc
    periodicHypercubicOrientedReciprocalPlaquetteScale sideLength *
          ENNReal.ofReal
            ((periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
              sideLength N sideLength_pos hN beta beta_nonneg).base.wilsonAction A) ≤
        periodicHypercubicOrientedReciprocalPlaquetteScale sideLength *
          (periodicHypercubicOrientedPlaquetteVolume sideLength * 2) :=
      mul_le_mul_left'
        (periodicHypercubicSpecialUnitaryWilsonActionObservable_le_volume_mul_two
          sideLength N sideLength_pos hN beta beta_nonneg A) _
    _ =
        (periodicHypercubicOrientedReciprocalPlaquetteScale sideLength *
          periodicHypercubicOrientedPlaquetteVolume sideLength) * 2 := by
      rw [mul_assoc]
    _ = 2 := by
      rw [periodicHypercubicOrientedReciprocalPlaquetteScale_mul_volume
        sideLength sideLength_pos]
      simp

end

end MathlibAnalytic
end MGAP4D
