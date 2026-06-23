import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianSemigroupCovariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every completed physical time operator is pointwise contractive. -/
theorem physicalOperator_norm_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤ ‖psi‖ := by
  calc
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤
        ‖T.toPhysicalSemigroup.operator t‖ * ‖psi‖ :=
      (T.toPhysicalSemigroup.operator t).le_opNorm psi
    _ ≤ 1 * ‖psi‖ :=
      mul_le_mul_of_nonneg_right
        (T.toPhysicalSemigroup.opNorm_le t) (norm_nonneg psi)
    _ = ‖psi‖ := one_mul _

/-- Every completed physical time operator contracts distances. -/
theorem physicalOperator_dist_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) (psi phi : P.PhysicalHilbert) :
    dist (T.toPhysicalSemigroup.operator t psi)
        (T.toPhysicalSemigroup.operator t phi) ≤ dist psi phi := by
  simpa only [dist_eq_norm, map_sub] using
    T.physicalOperator_norm_le t (psi - phi)

/-- In `NNReal`, subtracting a smaller time converts distance to zero into the
original distance. -/
theorem nnreal_dist_tsub_zero_eq
    {s t : NNReal} (hts : t ≤ s) :
    dist (s - t) 0 = dist s t := by
  have hreal : (t : ℝ) ≤ (s : ℝ) := by exact_mod_cast hts
  change dist (((s - t : NNReal) : ℝ)) (0 : ℝ) =
    dist (s : ℝ) (t : ℝ)
  rw [NNReal.coe_sub hts]
  simp [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hreal)]

/-- Strong continuity at zero and contractivity imply continuity of every
physical orbit at every nonnegative Euclidean time. -/
theorem physicalOrbit_continuousAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) :
    ContinuousAt
      (fun s : NNReal => T.toPhysicalSemigroup.operator s psi) t := by
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  rcases Metric.continuousAt_iff.mp
      (T.strongContinuousAt_zero psi) epsilon hepsilon with
    ⟨delta, hdelta, hzero⟩
  refine ⟨delta, hdelta, ?_⟩
  intro s hst
  have hzero' :
      ∀ u : NNReal, dist u 0 < delta →
        dist (T.toPhysicalSemigroup.operator u psi) psi < epsilon := by
    intro u hu
    have h := hzero hu
    rw [T.toPhysicalSemigroup.operator_zero] at h
    exact h
  rcases le_total t s with hts | hst_le
  · have hu : dist (s - t) 0 < delta := by
      rw [T.nnreal_dist_tsub_zero_eq hts]
      exact hst
    have hsmall := hzero' (s - t) hu
    have hs : s = t + (s - t) := by
      rw [add_comm, tsub_add_cancel_of_le hts]
    calc
      dist (T.toPhysicalSemigroup.operator s psi)
          (T.toPhysicalSemigroup.operator t psi) =
        dist
          (T.toPhysicalSemigroup.operator t
            (T.toPhysicalSemigroup.operator (s - t) psi))
          (T.toPhysicalSemigroup.operator t psi) := by
            rw [hs, T.toPhysicalSemigroup.operator_add]
            rfl
      _ ≤ dist (T.toPhysicalSemigroup.operator (s - t) psi) psi :=
        T.physicalOperator_dist_le t _ _
      _ < epsilon := hsmall
  · have hu : dist (t - s) 0 < delta := by
      rw [T.nnreal_dist_tsub_zero_eq hst_le]
      simpa [dist_comm] using hst
    have hsmall := hzero' (t - s) hu
    have ht : t = s + (t - s) := by
      rw [add_comm, tsub_add_cancel_of_le hst_le]
    calc
      dist (T.toPhysicalSemigroup.operator s psi)
          (T.toPhysicalSemigroup.operator t psi) =
        dist (T.toPhysicalSemigroup.operator s psi)
          (T.toPhysicalSemigroup.operator s
            (T.toPhysicalSemigroup.operator (t - s) psi)) := by
            rw [ht, T.toPhysicalSemigroup.operator_add]
            rfl
      _ ≤ dist psi (T.toPhysicalSemigroup.operator (t - s) psi) :=
        T.physicalOperator_dist_le s _ _
      _ = dist (T.toPhysicalSemigroup.operator (t - s) psi) psi :=
        dist_comm _ _
      _ < epsilon := hsmall

/-- Every vector orbit of the completed physical contraction semigroup is
continuous on all nonnegative Euclidean times. -/
theorem physicalOrbit_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous
      (fun t : NNReal => T.toPhysicalSemigroup.operator t psi) := by
  rw [continuous_iff_continuousAt]
  exact T.physicalOrbit_continuousAt psi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
