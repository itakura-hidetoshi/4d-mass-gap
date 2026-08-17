import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationTimeAverage

/-!
# Multiplicative midpoint inequality for physical OS correlations

Symmetry and the semigroup law identify a correlation at a sum of Euclidean
times with the inner product of the two evolved vectors.  Applying this at the
half-times `s / 2` and `t / 2`, followed by the real Hilbert-space
Cauchy--Schwarz inequality, gives

`C((s+t)/2)^2 ≤ C(s) C(t)`.

This is the multiplicative midpoint (log-convex type) inequality for the actual
completed physical OS autocorrelation.  It is strictly stronger than the
additive midpoint-convexity inequality and uses no spectral theorem,
differentiability, decay estimate, or additional physical assumption.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Symmetry moves one semigroup factor to the first slot: the correlation at
`s+t` is the inner product of the two separately evolved states. -/
theorem physicalCorrelation_add_eq_inner_operators
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.physicalCorrelation psi (s + t) =
      inner ℝ
        (T.toPhysicalSemigroup.operator s psi)
        (T.toPhysicalSemigroup.operator t psi) := by
  unfold physicalCorrelation
  rw [T.toPhysicalSemigroup.operator_add]
  exact
    (hSymmetric s psi (T.toPhysicalSemigroup.operator t psi)).symm

/-- Multiplicative midpoint inequality for every pair of nonnegative Euclidean
times. -/
theorem physicalCorrelation_midpoint_sq_le_mul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.physicalCorrelation psi ((s + t) / 2) ^ 2 ≤
      T.physicalCorrelation psi s * T.physicalCorrelation psi t := by
  let u := T.toPhysicalSemigroup.operator (s / 2) psi
  let v := T.toPhysicalSemigroup.operator (t / 2) psi
  have hmidTime : s / 2 + t / 2 = (s + t) / 2 := by
    apply NNReal.eq
    ring
  have hsTime : s / 2 + s / 2 = s := by
    apply NNReal.eq
    ring
  have htTime : t / 2 + t / 2 = t := by
    apply NNReal.eq
    ring
  have hmid :
      T.physicalCorrelation psi ((s + t) / 2) = inner ℝ u v := by
    rw [← hmidTime]
    exact T.physicalCorrelation_add_eq_inner_operators
      hSymmetric (s / 2) (t / 2) psi
  have hsCorr : T.physicalCorrelation psi s = ‖u‖ ^ 2 := by
    rw [← hsTime]
    exact T.physicalCorrelation_add_self_eq_norm_sq
      hSymmetric (s / 2) psi
  have htCorr : T.physicalCorrelation psi t = ‖v‖ ^ 2 := by
    rw [← htTime]
    exact T.physicalCorrelation_add_self_eq_norm_sq
      hSymmetric (t / 2) psi
  have hcauchy : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have hinnerNonneg : 0 ≤ inner ℝ u v := by
    rw [← hmid]
    exact T.physicalCorrelation_nonneg hSymmetric ((s + t) / 2) psi
  have hprodNonneg : 0 ≤ ‖u‖ * ‖v‖ :=
    mul_nonneg (norm_nonneg u) (norm_nonneg v)
  have hfactor :
      0 ≤ (‖u‖ * ‖v‖ - inner ℝ u v) *
        (‖u‖ * ‖v‖ + inner ℝ u v) :=
    mul_nonneg (sub_nonneg.mpr hcauchy)
      (add_nonneg hprodNonneg hinnerNonneg)
  rw [hmid, hsCorr, htCorr]
  nlinarith

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
