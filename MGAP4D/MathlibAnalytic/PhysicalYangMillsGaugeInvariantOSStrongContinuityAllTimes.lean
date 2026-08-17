import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassOrbitDifferentialInequality
import Mathlib.Tactic

/-!
# Strong continuity of the physical OS semigroup at every nonnegative time

The physical semigroup is constructed with strong continuity at time zero.
For a contraction semigroup on `NNReal`, that already forces strong continuity
at every nonnegative time.  This file derives the global orbit-continuity layer
needed to pass the right-generator differential inequality to Mathlib's real-time
Gronwall theorem.

No new analytic or physical assumption is introduced: only the additive
semigroup law, the operator-norm contraction bound, and the existing strong
continuity at zero are used.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every completed physical time-translation is pointwise contractive. -/
theorem physicalOperator_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤ ‖psi‖ := by
  by_cases hpsi : psi = 0
  · simp [hpsi]
  · have hpos : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi
    have hratio :=
      (T.toPhysicalSemigroup.operator t).le_opNorm psi
    have happly :
        ‖T.toPhysicalSemigroup.operator t psi‖ ≤
          ‖T.toPhysicalSemigroup.operator t‖ * ‖psi‖ :=
      (div_le_iff₀ hpos).mp hratio
    calc
      ‖T.toPhysicalSemigroup.operator t psi‖ ≤
          ‖T.toPhysicalSemigroup.operator t‖ * ‖psi‖ := happly
      _ ≤ 1 * ‖psi‖ :=
        mul_le_mul_of_nonneg_right
          (T.toPhysicalSemigroup.opNorm_le t) (norm_nonneg psi)
      _ = ‖psi‖ := one_mul _

/-- The time increment `t - s` has distance to zero exactly the distance from
`t` to `s` whenever `s ≤ t`. -/
private theorem dist_tsub_zero_eq_dist_of_le
    {s t : NNReal} (hst : s ≤ t) :
    dist (t - s) 0 = dist t s := by
  rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_sub hst]
  simp [abs_of_nonneg (sub_nonneg.mpr hst)]

/-- The time increment `s - t` has distance to zero exactly the distance from
`t` to `s` whenever `t ≤ s`. -/
private theorem dist_tsub_zero_eq_dist_of_ge
    {s t : NNReal} (hts : t ≤ s) :
    dist (s - t) 0 = dist t s := by
  rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_sub hts]
  simp [abs_of_nonneg (sub_nonneg.mpr hts), abs_sub_comm]

/-- Strong continuity at zero plus contractivity and the semigroup law imply
strong continuity of every physical orbit at every `s : NNReal`. -/
theorem strongContinuousAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s : NNReal) :
    ContinuousAt
      (fun t : NNReal => T.toPhysicalSemigroup.operator t psi) s := by
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  rcases Metric.continuousAt_iff.mp
      (T.strongContinuousAt_zero psi) epsilon hepsilon with
    ⟨delta, hdelta, hzero⟩
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  by_cases hst : s ≤ t
  · have hinc : dist (t - s) 0 < delta := by
      rw [dist_tsub_zero_eq_dist_of_le hst]
      exact ht
    have hzero' := hzero hinc
    rw [T.toPhysicalSemigroup.operator_zero] at hzero'
    have htadd : s + (t - s) = t := add_tsub_cancel_of_le hst
    calc
      dist (T.toPhysicalSemigroup.operator t psi)
          (T.toPhysicalSemigroup.operator s psi) =
          dist
            (T.toPhysicalSemigroup.operator s
              (T.toPhysicalSemigroup.operator (t - s) psi))
            (T.toPhysicalSemigroup.operator s psi) := by
              rw [← htadd, T.toPhysicalSemigroup.operator_add]
              rfl
      _ = ‖T.toPhysicalSemigroup.operator s
            (T.toPhysicalSemigroup.operator (t - s) psi - psi)‖ := by
              rw [dist_eq_norm, map_sub]
      _ ≤ ‖T.toPhysicalSemigroup.operator (t - s) psi - psi‖ :=
        T.physicalOperator_norm_le s
          (T.toPhysicalSemigroup.operator (t - s) psi - psi)
      _ = dist (T.toPhysicalSemigroup.operator (t - s) psi) psi := by
        rw [dist_eq_norm]
      _ < epsilon := by simpa using hzero'
  · have hts : t ≤ s := le_of_not_ge hst
    have hinc : dist (s - t) 0 < delta := by
      rw [dist_tsub_zero_eq_dist_of_ge hts]
      exact ht
    have hzero' := hzero hinc
    rw [T.toPhysicalSemigroup.operator_zero] at hzero'
    have hsadd : t + (s - t) = s := add_tsub_cancel_of_le hts
    calc
      dist (T.toPhysicalSemigroup.operator t psi)
          (T.toPhysicalSemigroup.operator s psi) =
          dist
            (T.toPhysicalSemigroup.operator t psi)
            (T.toPhysicalSemigroup.operator t
              (T.toPhysicalSemigroup.operator (s - t) psi)) := by
              rw [← hsadd, T.toPhysicalSemigroup.operator_add]
              rfl
      _ = ‖T.toPhysicalSemigroup.operator t
            (psi - T.toPhysicalSemigroup.operator (s - t) psi)‖ := by
              rw [dist_eq_norm, map_sub]
      _ ≤ ‖psi - T.toPhysicalSemigroup.operator (s - t) psi‖ :=
        T.physicalOperator_norm_le t
          (psi - T.toPhysicalSemigroup.operator (s - t) psi)
      _ = dist psi (T.toPhysicalSemigroup.operator (s - t) psi) := by
        rw [dist_eq_norm]
      _ = dist (T.toPhysicalSemigroup.operator (s - t) psi) psi :=
        dist_comm _ _
      _ < epsilon := by simpa using hzero'

/-- Hence every completed physical orbit is continuous on the whole
nonnegative-time half-line. -/
theorem strongContinuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous
      (fun t : NNReal => T.toPhysicalSemigroup.operator t psi) :=
  continuous_iff_continuousAt.mpr (T.strongContinuousAt psi)

/-- Squared orbit norms are continuous on the nonnegative-time half-line. -/
theorem physicalOrbitNormSq_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous
      (fun t : NNReal => ‖T.toPhysicalSemigroup.operator t psi‖ ^ 2) := by
  fun_prop

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
