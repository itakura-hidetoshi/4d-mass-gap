import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedDiscreteTemporalActionCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

variable {E : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}

@[simp]
theorem latticeTranslate_neg_apply
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ)
    (U : (E.system n).base.Configuration) :
    A.latticeTranslate n (-k) (A.latticeTranslate n k U) = U := by
  calc
    A.latticeTranslate n (-k) (A.latticeTranslate n k U) =
        A.latticeTranslate n ((-k) + k) U :=
      (A.latticeTranslate_add_apply n (-k) k U).symm
    _ = A.latticeTranslate n 0 U := by rw [neg_add_cancel]
    _ = U := A.latticeTranslate_zero_apply n U

@[simp]
theorem latticeTranslate_apply_neg
    (A : E.PhysicalDiscreteTemporalAction) (n : ℕ) (k : ℤ)
    (U : (E.system n).base.Configuration) :
    A.latticeTranslate n k (A.latticeTranslate n (-k) U) = U := by
  calc
    A.latticeTranslate n k (A.latticeTranslate n (-k) U) =
        A.latticeTranslate n (k + (-k)) U :=
      (A.latticeTranslate_add_apply n k (-k) U).symm
    _ = A.latticeTranslate n 0 U := by rw [add_neg_cancel]
    _ = U := A.latticeTranslate_zero_apply n U

end ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding.PhysicalDiscreteTemporalAction

end

end MathlibAnalytic
end MGAP4D
