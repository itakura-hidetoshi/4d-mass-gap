import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusResidualSliceGaugeAction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Applying the same residual gauge transformation to two spatial slices
preserves equality at each individual spatial link. -/
@[simp] theorem finiteEvenFourTorusZ2ResidualSlice_smul_apply_eq_iff
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    (g • A) e = (g • B) e ↔ A e = B e := by
  constructor
  · intro hEq
    have hCancel := congrArg
      (fun z : Z2Gauge =>
        (g e.1)⁻¹ * z *
          g (finiteEvenFourTorusSpatialVertexStep H e.1 e.2)) hEq
    simpa [finiteEvenFourTorusZ2ResidualSlice_smul_apply, mul_assoc] using hCancel
  · intro hEq
    simp [finiteEvenFourTorusZ2ResidualSlice_smul_apply, hEq]

/-- Applying the same residual gauge transformation preserves linkwise
disagreement. -/
@[simp] theorem finiteEvenFourTorusZ2ResidualSlice_smul_apply_ne_iff
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    (g • A) e ≠ (g • B) e ↔ A e ≠ B e := by
  simpa only [ne_eq,
    finiteEvenFourTorusZ2ResidualSlice_smul_apply_eq_iff]

/-- The complete finite disagreement set is invariant under the diagonal
residual gauge action. -/
theorem finiteProductDisagreementFinset_residualGauge_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteProductDisagreementFinset (g • A) (g • B) =
      finiteProductDisagreementFinset A B := by
  ext e
  simp [finiteProductDisagreementFinset]

/-- Residual gauge transformations act by exact Hamming isometries on the
finite spatial-slice configuration space. -/
theorem finiteProductHammingDistanceReal_residualGauge_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteProductHammingDistanceReal (g • A) (g • B) =
      finiteProductHammingDistanceReal A B := by
  unfold finiteProductHammingDistanceReal
  rw [finiteProductDisagreementFinset_residualGauge_smul H g A B]

/-- Moving one residual gauge transform from the left argument to the right
argument replaces it by the inverse transform. -/
theorem finiteProductHammingDistanceReal_residualGauge_smul_left
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteProductHammingDistanceReal (g • A) B =
      finiteProductHammingDistanceReal A (g⁻¹ • B) := by
  calc
    finiteProductHammingDistanceReal (g • A) B =
        finiteProductHammingDistanceReal
          (g⁻¹ • (g • A)) (g⁻¹ • B) := by
      symm
      exact finiteProductHammingDistanceReal_residualGauge_smul
        H g⁻¹ (g • A) B
    _ = finiteProductHammingDistanceReal A (g⁻¹ • B) := by
      simp [smul_smul]

/-- Hamming distance between differently gauge-transformed slices depends
only on their relative residual gauge transformation. -/
theorem finiteProductHammingDistanceReal_residualGauge_relative
    (H : ℕ)
    (g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteProductHammingDistanceReal (g • A) (h • B) =
      finiteProductHammingDistanceReal A ((g⁻¹ * h) • B) := by
  rw [finiteProductHammingDistanceReal_residualGauge_smul_left H g A (h • B)]
  rw [← mul_smul]

/-- Public package for the exact residual-gauge Hamming isometry and relative
gauge reduction. -/
theorem finiteEvenFourTorusZ2ResidualGaugeHammingIsometryPackage
    (H : ℕ) :
    (∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
      ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteProductHammingDistanceReal (g • A) (g • B) =
        finiteProductHammingDistanceReal A B) ∧
    (∀ g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
      ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteProductHammingDistanceReal (g • A) (h • B) =
        finiteProductHammingDistanceReal A ((g⁻¹ * h) • B)) := by
  exact ⟨
    finiteProductHammingDistanceReal_residualGauge_smul H,
    finiteProductHammingDistanceReal_residualGauge_relative H⟩

end

end MathlibAnalytic
end MGAP4D
