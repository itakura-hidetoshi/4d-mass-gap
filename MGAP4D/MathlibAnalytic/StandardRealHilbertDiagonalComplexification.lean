import MGAP4D.MathlibAnalytic.StandardRealHilbertComplexificationL2CoordinatesComplete
import Mathlib.Analysis.Normed.Operator.Prod

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Coordinatewise action of a bounded real-linear operator on the `L²` coordinate model. -/
noncomputable def diagonalL2 (T : H →L[ℝ] H) :
    WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ H H).symm.toContinuousLinearMap.comp
    ((T.prodMap T).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ H H).toContinuousLinearMap)

@[simp]
theorem diagonalL2_apply
    (T : H →L[ℝ] H) (z : WithLp 2 (H × H)) :
    diagonalL2 T z = WithLp.toLp 2 (T z.fst, T z.snd) :=
  rfl

/-- The algebraic diagonal complexification of a bounded real-linear operator. -/
def diagonalComplexificationLinearMap (T : H →L[ℝ] H) :
    StandardRealHilbertComplexification H →ₗ[ℂ]
      StandardRealHilbertComplexification H where
  toFun z := (T z.1, T z.2)
  map_add' z w := by
    apply Prod.ext <;> simp
  map_smul' c z := by
    apply Prod.ext <;>
      simp [complex_smul_re, complex_smul_im]

/-- A bounded real-linear operator acts diagonally on the standard complexification as a bounded
complex-linear operator. -/
noncomputable def diagonalComplexification (T : H →L[ℝ] H) :
    StandardRealHilbertComplexification H →L[ℂ]
      StandardRealHilbertComplexification H where
  toLinearMap := diagonalComplexificationLinearMap T
  cont := by
    let e := coordinatesL2ContinuousLinearEquiv (H := H)
    let d := diagonalL2 T
    have h : Continuous fun z : StandardRealHilbertComplexification H =>
        e.symm (d (e z)) :=
      e.symm.continuous.comp (d.continuous.comp e.continuous)
    simpa [e, d] using h

@[simp]
theorem diagonalComplexification_apply
    (T : H →L[ℝ] H) (z : StandardRealHilbertComplexification H) :
    diagonalComplexification T z = (T z.1, T z.2) :=
  rfl

@[simp]
theorem diagonalComplexification_re
    (T : H →L[ℝ] H) (z : StandardRealHilbertComplexification H) :
    (diagonalComplexification T z).1 = T z.1 :=
  rfl

@[simp]
theorem diagonalComplexification_im
    (T : H →L[ℝ] H) (z : StandardRealHilbertComplexification H) :
    (diagonalComplexification T z).2 = T z.2 :=
  rfl

@[simp]
theorem diagonalComplexification_ofReal
    (T : H →L[ℝ] H) (x : H) :
    diagonalComplexification T (ofReal x) = ofReal (T x) := by
  apply Prod.ext <;> simp [ofReal]

@[simp]
theorem diagonalComplexification_conjugation
    (T : H →L[ℝ] H) (z : StandardRealHilbertComplexification H) :
    diagonalComplexification T (conjugation z) =
      conjugation (diagonalComplexification T z) := by
  apply Prod.ext <;> simp [conjugation]

@[simp]
theorem diagonalComplexification_id :
    diagonalComplexification (ContinuousLinearMap.id ℝ H) =
      ContinuousLinearMap.id ℂ (StandardRealHilbertComplexification H) := by
  ext z <;> rfl

@[simp]
theorem diagonalComplexification_comp
    (S T : H →L[ℝ] H) :
    diagonalComplexification (S.comp T) =
      (diagonalComplexification S).comp (diagonalComplexification T) := by
  ext z <;> rfl

end StandardRealHilbertComplexification

end

end MathlibAnalytic
end MGAP4D
