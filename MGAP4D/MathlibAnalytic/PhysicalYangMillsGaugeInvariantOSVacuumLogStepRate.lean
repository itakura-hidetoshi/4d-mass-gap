import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumLogGeometricEnvelope
import Mathlib.Tactic

/-!
# One-step vacuum-sector rate below discrete physical OS log decay

The preceding logarithmic-envelope layer gives, at every positive discrete even
Euclidean time `n t + n t`, a lower bound for the normalized physical OS log
decay by the geometric envelope coming from iterated semigroup decay.

This file simplifies that geometric envelope exactly.  For a nonzero state
orthogonal to the physical vacuum,

`(L(0) - log (((decayFactor t)^n * ‖psi‖)^2)) / (2 n t)`

is exactly

`- log (decayFactor t) / t`.

Using `Real.log_le_sub_one_of_pos`, this further yields the infinitesimal
vacuum-gap slope bound

`t⁻¹ * (1 - decayFactor t) ≤ normalizedLogDecay(2 n t)`.

No spectral theorem, PVM, exponential-decay hypothesis, self-adjointness
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

/-- The geometric-envelope logarithmic loss per discrete even time is exactly
the one-step logarithmic decay rate. -/
theorem VacuumSemigroupGapSlope.log_geometricEnvelope_div_time_eq_neg_log_decayFactor_div
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    (ht : 0 < t) (hn : 0 < n) :
    (T.physicalCorrelationRealClampLog psi 0 -
        Real.log (((G.decayFactor t) ^ n * ‖psi‖) ^ 2)) /
        (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) =
      - Real.log (G.decayFactor t) / (t : ℝ) := by
  have hd_pos : 0 < G.decayFactor t :=
    G.decayFactor_pos_of_orthogonal_ne_zero T hSymmetric t hpsi hpsi_ne
  have hd_ne : G.decayFactor t ≠ 0 := ne_of_gt hd_pos
  have hnorm_pos : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi_ne
  have hnorm_ne : ‖psi‖ ≠ 0 := ne_of_gt hnorm_pos
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have ht_ne : (t : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht)
  have hzero :
      T.physicalCorrelationRealClampLog psi 0 =
        2 * Real.log ‖psi‖ := by
    unfold physicalCorrelationRealClampLog
    have hclamp :
        T.physicalCorrelationRealClamp psi 0 = ‖psi‖ ^ 2 := by
      simpa using T.physicalCorrelationRealClamp_coe psi (0 : NNReal)
    rw [hclamp, Real.log_pow]
    norm_num
  have hpow_ne : (G.decayFactor t) ^ n ≠ 0 :=
    pow_ne_zero n hd_ne
  have hprod_ne : (G.decayFactor t) ^ n * ‖psi‖ ≠ 0 :=
    mul_ne_zero hpow_ne hnorm_ne
  have henvelope :
      Real.log (((G.decayFactor t) ^ n * ‖psi‖) ^ 2) =
        2 * ((n : ℝ) * Real.log (G.decayFactor t) +
          Real.log ‖psi‖) := by
    rw [Real.log_pow, Real.log_mul hpow_ne hnorm_ne, Real.log_pow]
    norm_num
  have htime :
      (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) =
        2 * (n : ℝ) * (t : ℝ) := by
    norm_num
    ring
  rw [hzero, henvelope, htime]
  field_simp [hn_ne, ht_ne]
  ring

/-- The one-step logarithmic decay rate is below every positive discrete-even
normalized physical OS logarithmic decay. -/
theorem VacuumSemigroupGapSlope.neg_log_decayFactor_div_le_normalizedLogDecayFromZero_nat_mul_add_self
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    (ht : 0 < t) (hn : 0 < n) :
    - Real.log (G.decayFactor t) / (t : ℝ) ≤
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero psi
        (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) := by
  rw [← G.log_geometricEnvelope_div_time_eq_neg_log_decayFactor_div
    T hSymmetric t n hpsi hpsi_ne ht hn]
  exact
    G.log_geometricEnvelope_div_time_le_normalizedLogDecayFromZero_nat_mul_add_self
      T hSymmetric t n hpsi hpsi_ne ht hn

/-- The infinitesimal vacuum-gap slope itself is below every positive
discrete-even normalized physical OS logarithmic decay. -/
theorem VacuumSemigroupGapSlope.slope_le_normalizedLogDecayFromZero_nat_mul_add_self
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (n : ℕ) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    (ht : 0 < t) (hn : 0 < n) :
    (t : ℝ)⁻¹ * (1 - G.decayFactor t) ≤
      T.physicalCorrelationRealClampNormalizedLogDecayFromZero psi
        (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) := by
  have hd_pos : 0 < G.decayFactor t :=
    G.decayFactor_pos_of_orthogonal_ne_zero T hSymmetric t hpsi hpsi_ne
  have hlog :
      Real.log (G.decayFactor t) ≤ G.decayFactor t - 1 :=
    Real.log_le_sub_one_of_pos hd_pos
  have hneg :
      1 - G.decayFactor t ≤ - Real.log (G.decayFactor t) := by
    linarith
  have ht_real : 0 < (t : ℝ) := by
    exact_mod_cast ht
  have hinv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr ht_real.le
  have hslope :
      (t : ℝ)⁻¹ * (1 - G.decayFactor t) ≤
        (t : ℝ)⁻¹ * (- Real.log (G.decayFactor t)) :=
    mul_le_mul_of_nonneg_left hneg hinv
  calc
    (t : ℝ)⁻¹ * (1 - G.decayFactor t) ≤
        (t : ℝ)⁻¹ * (- Real.log (G.decayFactor t)) := hslope
    _ = - Real.log (G.decayFactor t) / (t : ℝ) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ T.physicalCorrelationRealClampNormalizedLogDecayFromZero psi
          (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) :=
      G.neg_log_decayFactor_div_le_normalizedLogDecayFromZero_nat_mul_add_self
        T hSymmetric t n hpsi hpsi_ne ht hn

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
