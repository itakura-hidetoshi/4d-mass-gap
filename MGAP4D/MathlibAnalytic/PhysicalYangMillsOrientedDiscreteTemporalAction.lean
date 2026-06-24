import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedLatticeEmbedding

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function

noncomputable section

/-- A scale-separated temporal-action interface.

At lattice scale `n`, only integer steps are used.  The additive homomorphism
`latticeTime n : ℤ →+ ℝ` records the corresponding physical times.  Thus the
interface does not require a floor or rounding map from all real times to lattice
steps, and it does not claim that such a map preserves addition. -/
structure ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction
    (E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding) where
  physicalTranslate : ℝ → Homeomorph E.PhysicalConfiguration E.PhysicalConfiguration
  physicalTranslate_zero_apply : ∀ A, physicalTranslate 0 A = A
  physicalTranslate_add_apply : ∀ s t A,
    physicalTranslate (s + t) A = physicalTranslate s (physicalTranslate t A)
  latticeTime : ∀ n, ℤ →+ ℝ
  latticeTranslate : ∀ n, ℤ →
    (E.system n).base.Configuration → (E.system n).base.Configuration
  latticeTranslate_measurable : ∀ n k, Measurable (latticeTranslate n k)
  latticeTranslate_zero_apply : ∀ n U, latticeTranslate n 0 U = U
  latticeTranslate_add_apply : ∀ n k l U,
    latticeTranslate n (k + l) U =
      latticeTranslate n k (latticeTranslate n l U)
  latticeGibbs_map_eq_self : ∀ n k,
    Measure.map (latticeTranslate n k) (E.system n).gibbsMeasure =
      (E.system n).gibbsMeasure
  interpolate_equivariant : ∀ n k U,
    E.interpolate n (latticeTranslate n k U) =
      physicalTranslate (latticeTime n k) (E.interpolate n U)

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

/-- The physical action at the zero lattice time is the identity. -/
@[simp]
theorem physicalTranslate_latticeTime_zero_apply
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ)
    (X : E.PhysicalConfiguration) :
    A.physicalTranslate (A.latticeTime n 0) X = X := by
  simpa using A.physicalTranslate_zero_apply X

/-- Addition of integer steps agrees with composition of the physical action at
realizable lattice times. -/
theorem physicalTranslate_latticeTime_add_apply
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k l : ℤ)
    (X : E.PhysicalConfiguration) :
    A.physicalTranslate (A.latticeTime n (k + l)) X =
      A.physicalTranslate (A.latticeTime n k)
        (A.physicalTranslate (A.latticeTime n l) X) := by
  rw [map_add]
  exact A.physicalTranslate_add_apply
    (A.latticeTime n k) (A.latticeTime n l) X

/-- Translation by the negative integer step is a left inverse on the finite
configuration space. -/
@[simp]
theorem latticeTranslate_neg_apply
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ)
    (U : (E.system n).base.Configuration) :
    A.latticeTranslate n (-k) (A.latticeTranslate n k U) = U := by
  simpa using (A.latticeTranslate_add_apply n (-k) k U).symm

/-- Translation by the negative integer step is also a right inverse. -/
@[simp]
theorem latticeTranslate_apply_neg
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ)
    (U : (E.system n).base.Configuration) :
    A.latticeTranslate n k (A.latticeTranslate n (-k) U) = U := by
  simpa using (A.latticeTranslate_add_apply n k (-k) U).symm

/-- Exact interpolation covariance at a realizable lattice time, written as a
composition identity. -/
theorem physicalTranslate_latticeTime_comp_interpolate
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ) :
    A.physicalTranslate (A.latticeTime n k) ∘ E.interpolate n =
      E.interpolate n ∘ A.latticeTranslate n k := by
  funext U
  exact (A.interpolate_equivariant n k U).symm

/-- Every embedded finite-volume law is invariant at every realizable lattice
time `latticeTime n k`. -/
theorem embeddedMeasure_toMeasure_map_latticeTime_eq_self
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ) :
    Measure.map (A.physicalTranslate (A.latticeTime n k))
        (ProbabilityMeasure.toMeasure
          (E.toLatticeEmbedding.embeddedMeasure n)) =
      ProbabilityMeasure.toMeasure
        (E.toLatticeEmbedding.embeddedMeasure n) := by
  change
    Measure.map (A.physicalTranslate (A.latticeTime n k))
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map (E.interpolate n) (E.system n).gibbsMeasure
  calc
    Measure.map (A.physicalTranslate (A.latticeTime n k))
        (Measure.map (E.interpolate n) (E.system n).gibbsMeasure) =
      Measure.map
        (A.physicalTranslate (A.latticeTime n k) ∘ E.interpolate n)
        (E.system n).gibbsMeasure :=
      Measure.map_map
        (A.physicalTranslate (A.latticeTime n k)).continuous.measurable
        (E.interpolate_measurable n)
    _ = Measure.map (E.interpolate n ∘ A.latticeTranslate n k)
        (E.system n).gibbsMeasure := by
      rw [A.physicalTranslate_latticeTime_comp_interpolate n k]
    _ = Measure.map (E.interpolate n)
        (Measure.map (A.latticeTranslate n k) (E.system n).gibbsMeasure) :=
      (Measure.map_map (E.interpolate_measurable n)
        (A.latticeTranslate_measurable n k)).symm
    _ = Measure.map (E.interpolate n) (E.system n).gibbsMeasure := by
      rw [A.latticeGibbs_map_eq_self]

/-- Probability-measure form of invariance at the exact scale-dependent lattice
times. -/
theorem embeddedMeasure_map_latticeTime_eq_self
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ) :
    (E.toLatticeEmbedding.embeddedMeasure n).map
        (A.physicalTranslate (A.latticeTime n k)).continuous.measurable.aemeasurable =
      E.toLatticeEmbedding.embeddedMeasure n := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  exact A.embeddedMeasure_toMeasure_map_latticeTime_eq_self n k

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

end

end MathlibAnalytic
end MGAP4D
