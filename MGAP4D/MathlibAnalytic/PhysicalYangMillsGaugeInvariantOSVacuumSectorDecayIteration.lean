import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCorrelationInfraredLogDecay
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteVolumeMassGapTransfer
import Mathlib.Tactic

/-!
# Iterated vacuum-sector decay for the physical OS semigroup

The continuum vacuum-sector gap package already supplies a one-step norm bound

`‖T_t psi‖ ≤ decayFactor t * ‖psi‖`

for states orthogonal to the physical vacuum.  This file records the two
structural facts needed to iterate that estimate without adding a spectral
assumption:

* OS inner-product symmetry together with vacuum invariance preserves vacuum
  orthogonality under every nonnegative Euclidean-time operator;
* for a nonzero vacuum-orthogonal state, the scalar one-step decay factor is
  nonnegative, so the one-step inequality may be multiplied inductively.

Consequently, at every fixed nonnegative time step `t`,

`‖T_{n t} psi‖ ≤ (decayFactor t)^n * ‖psi‖`.

This is the discrete semigroup bridge needed for the subsequent passage from
the infinitesimal gap slope to a long-time logarithmic decay lower bound.  No
spectral theorem, PVM, exponential-decay hypothesis, self-adjointness
assumption, or new physical axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Physical Euclidean-time evolution preserves orthogonality to the vacuum
once the completed OS semigroup is inner-product symmetric. -/
theorem physicalOperator_preserves_vacuum_orthogonality
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0) :
    inner ℝ (T.toPhysicalSemigroup.operator t psi) P.vacuum = 0 := by
  calc
    inner ℝ (T.toPhysicalSemigroup.operator t psi) P.vacuum =
        inner ℝ psi (T.toPhysicalSemigroup.operator t P.vacuum) :=
      hSymmetric t psi P.vacuum
    _ = inner ℝ psi P.vacuum := by
      rw [T.toPhysicalSemigroup.fixes_vacuum t]
    _ = 0 := hpsi

/-- On a nonzero vacuum-orthogonal state, every scalar decay factor appearing
in a `VacuumSemigroupGapSlope` package is nonnegative. -/
theorem VacuumSemigroupGapSlope.decayFactor_nonneg_of_orthogonal_ne_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    0 ≤ G.decayFactor t := by
  have hdecay := G.decay t psi hpsi
  have hnormPos : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi_ne
  have hnonneg :
      0 ≤ G.decayFactor t * ‖psi‖ :=
    le_trans (norm_nonneg (T.toPhysicalSemigroup.operator t psi)) hdecay
  nlinarith

/-- A fixed one-step vacuum-sector decay estimate iterates along the additive
physical OS semigroup. -/
theorem VacuumSemigroupGapSlope.decay_nat_mul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    ‖T.toPhysicalSemigroup.operator ((n : NNReal) * t) psi‖ ≤
      (G.decayFactor t) ^ n * ‖psi‖ := by
  have hd : 0 ≤ G.decayFactor t :=
    G.decayFactor_nonneg_of_orthogonal_ne_zero T t hpsi hpsi_ne
  induction n with
  | zero =>
      simp [T.toPhysicalSemigroup.operator_zero]
  | succ n ih =>
      have htime :
          (((Nat.succ n : ℕ) : NNReal) * t) =
            t + ((n : NNReal) * t) := by
        rw [Nat.cast_succ]
        ring
      have horth :
          inner ℝ
              (T.toPhysicalSemigroup.operator ((n : NNReal) * t) psi)
              P.vacuum = 0 :=
        T.physicalOperator_preserves_vacuum_orthogonality
          hSymmetric ((n : NNReal) * t) hpsi
      calc
        ‖T.toPhysicalSemigroup.operator (((Nat.succ n : ℕ) : NNReal) * t) psi‖ =
            ‖T.toPhysicalSemigroup.operator t
              (T.toPhysicalSemigroup.operator ((n : NNReal) * t) psi)‖ := by
          rw [htime, T.toPhysicalSemigroup.operator_add]
          rfl
        _ ≤ G.decayFactor t *
              ‖T.toPhysicalSemigroup.operator ((n : NNReal) * t) psi‖ :=
          G.decay t
            (T.toPhysicalSemigroup.operator ((n : NNReal) * t) psi)
            horth
        _ ≤ G.decayFactor t *
              ((G.decayFactor t) ^ n * ‖psi‖) :=
          mul_le_mul_of_nonneg_left ih hd
        _ = (G.decayFactor t) ^ (Nat.succ n) * ‖psi‖ := by
          rw [pow_succ]
          ring

/-- The finite-volume vacuum-gap transfer package inherits the same iterated
continuum decay estimate through its canonical `VacuumSemigroupGapSlope`
projection. -/
theorem FiniteVolumeVacuumGapTransfer.decay_nat_mul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    ‖T.toPhysicalSemigroup.operator ((n : NNReal) * t) psi‖ ≤
      (G.decayFactor t) ^ n * ‖psi‖ := by
  exact
    G.toVacuumSemigroupGapSlope.decay_nat_mul
      T hSymmetric t n hpsi hpsi_ne

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
