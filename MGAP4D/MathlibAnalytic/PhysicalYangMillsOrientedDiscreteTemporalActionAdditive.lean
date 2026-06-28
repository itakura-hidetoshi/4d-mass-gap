import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDiscreteTemporalActionCore

namespace MGAP4D
namespace MathlibAnalytic

open Function

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

@[simp]
theorem physicalTranslate_latticeTime_zero_apply
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ)
    (X : E.PhysicalConfiguration) :
    A.physicalTranslate (A.latticeTime n 0) X = X := by
  simpa using A.physicalTranslate_zero_apply X

theorem physicalTranslate_latticeTime_add_apply
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k l : ℤ)
    (X : E.PhysicalConfiguration) :
    A.physicalTranslate (A.latticeTime n (k + l)) X =
      A.physicalTranslate (A.latticeTime n k)
        (A.physicalTranslate (A.latticeTime n l) X) := by
  rw [map_add]
  exact A.physicalTranslate_add_apply
    (A.latticeTime n k) (A.latticeTime n l) X

theorem physicalTranslate_latticeTime_comp_interpolate
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ) :
    A.physicalTranslate (A.latticeTime n k) ∘ E.interpolate n =
      E.interpolate n ∘ A.latticeTranslate n k := by
  funext U
  exact (A.interpolate_equivariant n k U).symm

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

end

end MathlibAnalytic
end MGAP4D
