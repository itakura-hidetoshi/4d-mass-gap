import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSymmetricSemigroupCorrelationTimeAverage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Pointwise form of the semigroup law.  Keeping this wrapper separate avoids
repeated coercion noise from `ContinuousLinearMap.comp` in the defect algebra. -/
theorem physicalOperator_add_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator (s + t) psi =
      T.toPhysicalSemigroup.operator s
        (T.toPhysicalSemigroup.operator t psi) := by
  have h := congrArg (fun L => L psi)
    (T.toPhysicalSemigroup.operator_add s t)
  simpa only [ContinuousLinearMap.comp_apply] using h

/-- The bounded semigroup defect `(I - T_t) psi`, written at vector level so
that no additional operator-algebra structure is needed. -/
def physicalDefect
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) (psi : P.PhysicalHilbert) : P.PhysicalHilbert :=
  psi - T.toPhysicalSemigroup.operator t psi

/-- Symmetry of the semigroup makes every vector-level defect formally
symmetric for the real Hilbert inner product. -/
theorem physicalDefect_inner_eq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi phi : P.PhysicalHilbert) :
    inner ℝ (T.physicalDefect t psi) phi =
      inner ℝ psi (T.physicalDefect t phi) := by
  simp only [physicalDefect, inner_sub_left, inner_sub_right]
  rw [hSymmetric]

/-- Physical defects at two nonnegative times commute, because the underlying
semigroup operators commute. -/
theorem physicalDefect_commute
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.physicalDefect s (T.physicalDefect t psi) =
      T.physicalDefect t (T.physicalDefect s psi) := by
  have hst :
      T.toPhysicalSemigroup.operator s
          (T.toPhysicalSemigroup.operator t psi) =
        T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator s psi) := by
    calc
      T.toPhysicalSemigroup.operator s
          (T.toPhysicalSemigroup.operator t psi) =
        T.toPhysicalSemigroup.operator (s + t) psi :=
          (T.physicalOperator_add_apply s t psi).symm
      _ = T.toPhysicalSemigroup.operator (t + s) psi := by rw [add_comm]
      _ = T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator s psi) :=
          T.physicalOperator_add_apply t s psi
  unfold physicalDefect
  simp only [map_sub]
  rw [hst]
  module

/-- A semigroup operator commutes with every vector-level defect. -/
theorem physicalOperator_physicalDefect_commute
    (T : P.StronglyContinuousPhysicalSemigroup)
    (a t : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator a (T.physicalDefect t psi) =
      T.physicalDefect t (T.toPhysicalSemigroup.operator a psi) := by
  have hat :
      T.toPhysicalSemigroup.operator a
          (T.toPhysicalSemigroup.operator t psi) =
        T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator a psi) := by
    calc
      T.toPhysicalSemigroup.operator a
          (T.toPhysicalSemigroup.operator t psi) =
        T.toPhysicalSemigroup.operator (a + t) psi :=
          (T.physicalOperator_add_apply a t psi).symm
      _ = T.toPhysicalSemigroup.operator (t + a) psi := by rw [add_comm]
      _ = T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator a psi) :=
          T.physicalOperator_add_apply t a psi
  unfold physicalDefect
  simp only [map_sub]
  rw [hat]

/-- Additive-time factorization of the defect:
`I - T_{s+t} = (I - T_s) + T_s (I - T_t)`. -/
theorem physicalDefect_add
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.physicalDefect (s + t) psi =
      T.physicalDefect s psi +
        T.toPhysicalSemigroup.operator s (T.physicalDefect t psi) := by
  unfold physicalDefect
  rw [T.physicalOperator_add_apply s t psi]
  simp only [map_sub]
  module

/-- The quadratic defect is exactly a loss of squared norm at half time. -/
theorem inner_physicalDefect_self_eq_norm_sq_sub_half
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    inner ℝ psi (T.physicalDefect t psi) =
      ‖psi‖ ^ 2 -
        ‖T.toPhysicalSemigroup.operator (t / 2) psi‖ ^ 2 := by
  have ht : t / 2 + t / 2 = t := by
    apply NNReal.eq
    norm_num
  have hcorr := T.physicalCorrelation_add_self_eq_norm_sq
    hSymmetric (t / 2) psi
  rw [ht] at hcorr
  unfold physicalDefect
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  change ‖psi‖ ^ 2 - T.physicalCorrelation psi t = _
  rw [hcorr]

/-- Every semigroup defect has a nonnegative quadratic form.  The proof uses
only half-time evolution and the contraction estimate. -/
theorem inner_physicalDefect_self_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    0 ≤ inner ℝ psi (T.physicalDefect t psi) := by
  rw [T.inner_physicalDefect_self_eq_norm_sq_sub_half hSymmetric]
  have hnorm := T.physicalOperator_norm_le (t / 2) psi
  nlinarith [norm_nonneg psi,
    norm_nonneg (T.toPhysicalSemigroup.operator (t / 2) psi)]

/-- Triple contractive-defect positivity.  Algebraically this is the quadratic
form of

`(I - T_{s+t}) (I - T_s) (I - T_t)`.

Instead of invoking a general theorem about products of commuting positive
operators, split `I-T_{s+t}` as
`(I-T_s) + T_s(I-T_t)`.  The first term becomes the quadratic form of
`I-T_t` on `(I-T_s)psi`.  For the second term, move the two half-time factors
of `T_s` across the inner product and obtain the quadratic form of `I-T_s` on
`(I-T_t)T_{s/2}psi`.  Both are nonnegative by the preceding theorem. -/
theorem inner_triplePhysicalDefect_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    0 ≤ inner ℝ psi
      (T.physicalDefect (s + t)
        (T.physicalDefect s (T.physicalDefect t psi))) := by
  let x := T.physicalDefect s (T.physicalDefect t psi)
  rw [T.physicalDefect_add s t x, inner_add_right]
  apply add_nonneg
  · calc
      0 ≤ inner ℝ (T.physicalDefect s psi)
          (T.physicalDefect t (T.physicalDefect s psi)) :=
        T.inner_physicalDefect_self_nonneg hSymmetric t
          (T.physicalDefect s psi)
      _ = inner ℝ psi (T.physicalDefect s x) := by
        rw [← T.physicalDefect_inner_eq hSymmetric s]
        dsimp [x]
        rw [T.physicalDefect_commute s t]
  · let u := T.toPhysicalSemigroup.operator (s / 2) psi
    let y := T.physicalDefect t x
    have hs : s / 2 + s / 2 = s := by
      apply NNReal.eq
      norm_num
    have hopen :
        T.toPhysicalSemigroup.operator s y =
          T.toPhysicalSemigroup.operator (s / 2)
            (T.toPhysicalSemigroup.operator (s / 2) y) := by
      calc
        T.toPhysicalSemigroup.operator s y =
            T.toPhysicalSemigroup.operator (s / 2 + s / 2) y := by rw [hs]
        _ = T.toPhysicalSemigroup.operator (s / 2)
            (T.toPhysicalSemigroup.operator (s / 2) y) :=
          T.physicalOperator_add_apply (s / 2) (s / 2) y
    have hhalf :
        inner ℝ psi (T.toPhysicalSemigroup.operator s y) =
          inner ℝ u (T.toPhysicalSemigroup.operator (s / 2) y) := by
      rw [hopen]
      exact (hSymmetric (s / 2) psi
        (T.toPhysicalSemigroup.operator (s / 2) y)).symm
    rw [hhalf]
    have hcomm :
        T.toPhysicalSemigroup.operator (s / 2) y =
          T.physicalDefect t
            (T.physicalDefect s (T.physicalDefect t u)) := by
      dsimp [y, x, u]
      rw [T.physicalOperator_physicalDefect_commute,
        T.physicalOperator_physicalDefect_commute,
        T.physicalOperator_physicalDefect_commute]
    rw [hcomm]
    calc
      0 ≤ inner ℝ (T.physicalDefect t u)
          (T.physicalDefect s (T.physicalDefect t u)) :=
        T.inner_physicalDefect_self_nonneg hSymmetric s
          (T.physicalDefect t u)
      _ = inner ℝ u
          (T.physicalDefect t
            (T.physicalDefect s (T.physicalDefect t u))) := by
        exact T.physicalDefect_inner_eq hSymmetric t u
          (T.physicalDefect s (T.physicalDefect t u))

/-- Exact scalar expansion of the triple defect. -/
theorem inner_triplePhysicalDefect_eq_correlation_trapezoidDefect
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    inner ℝ psi
      (T.physicalDefect (s + t)
        (T.physicalDefect s (T.physicalDefect t psi))) =
      T.physicalCorrelation psi 0 - T.physicalCorrelation psi s -
        T.physicalCorrelation psi t +
        T.physicalCorrelation psi ((s + t) + s) +
        T.physicalCorrelation psi ((s + t) + t) -
        T.physicalCorrelation psi ((s + t) + (s + t)) := by
  have hst :
      T.toPhysicalSemigroup.operator s
          (T.toPhysicalSemigroup.operator t psi) =
        T.toPhysicalSemigroup.operator (s + t) psi :=
    (T.physicalOperator_add_apply s t psi).symm
  have hht :
      T.toPhysicalSemigroup.operator (s + t)
          (T.toPhysicalSemigroup.operator t psi) =
        T.toPhysicalSemigroup.operator ((s + t) + t) psi :=
    (T.physicalOperator_add_apply (s + t) t psi).symm
  have hhs :
      T.toPhysicalSemigroup.operator (s + t)
          (T.toPhysicalSemigroup.operator s psi) =
        T.toPhysicalSemigroup.operator ((s + t) + s) psi :=
    (T.physicalOperator_add_apply (s + t) s psi).symm
  have hhh :
      T.toPhysicalSemigroup.operator (s + t)
          (T.toPhysicalSemigroup.operator s
            (T.toPhysicalSemigroup.operator t psi)) =
        T.toPhysicalSemigroup.operator ((s + t) + (s + t)) psi := by
    rw [hst]
    exact (T.physicalOperator_add_apply (s + t) (s + t) psi).symm
  calc
    inner ℝ psi
        (T.physicalDefect (s + t)
          (T.physicalDefect s (T.physicalDefect t psi))) =
      inner ℝ psi psi -
        inner ℝ psi (T.toPhysicalSemigroup.operator t psi) -
        inner ℝ psi (T.toPhysicalSemigroup.operator s psi) +
        inner ℝ psi
          (T.toPhysicalSemigroup.operator s
            (T.toPhysicalSemigroup.operator t psi)) -
        inner ℝ psi (T.toPhysicalSemigroup.operator (s + t) psi) +
        inner ℝ psi
          (T.toPhysicalSemigroup.operator (s + t)
            (T.toPhysicalSemigroup.operator t psi)) +
        inner ℝ psi
          (T.toPhysicalSemigroup.operator (s + t)
            (T.toPhysicalSemigroup.operator s psi)) -
        inner ℝ psi
          (T.toPhysicalSemigroup.operator (s + t)
            (T.toPhysicalSemigroup.operator s
              (T.toPhysicalSemigroup.operator t psi))) := by
      unfold physicalDefect
      simp only [map_sub, inner_sub_right]
      ring
    _ = inner ℝ psi psi -
        inner ℝ psi (T.toPhysicalSemigroup.operator t psi) -
        inner ℝ psi (T.toPhysicalSemigroup.operator s psi) +
        inner ℝ psi (T.toPhysicalSemigroup.operator (s + t) psi) -
        inner ℝ psi (T.toPhysicalSemigroup.operator (s + t) psi) +
        inner ℝ psi (T.toPhysicalSemigroup.operator ((s + t) + t) psi) +
        inner ℝ psi (T.toPhysicalSemigroup.operator ((s + t) + s) psi) -
        inner ℝ psi
          (T.toPhysicalSemigroup.operator ((s + t) + (s + t)) psi) := by
      rw [hst, hht, hhs, hhh]
    _ = T.physicalCorrelation psi 0 - T.physicalCorrelation psi s -
        T.physicalCorrelation psi t +
        T.physicalCorrelation psi ((s + t) + s) +
        T.physicalCorrelation psi ((s + t) + t) -
        T.physicalCorrelation psi ((s + t) + (s + t)) := by
      unfold physicalCorrelation
      simp only [T.toPhysicalSemigroup.operator_zero]
      ring

/-- Pairwise trapezoid inequality for symmetric contraction-semigroup
correlations.  This is the pointwise estimate whose interval integral gives the
no-loss time-average Hamiltonian numerator bound. -/
theorem physicalCorrelation_pair_trapezoid_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    (T.physicalCorrelation psi s -
        T.physicalCorrelation psi ((s + t) + s)) +
      (T.physicalCorrelation psi t -
        T.physicalCorrelation psi ((s + t) + t)) ≤
      T.physicalCorrelation psi 0 -
        T.physicalCorrelation psi ((s + t) + (s + t)) := by
  have hnonneg := T.inner_triplePhysicalDefect_nonneg
    hSymmetric s t psi
  rw [T.inner_triplePhysicalDefect_eq_correlation_trapezoidDefect] at hnonneg
  linarith

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
