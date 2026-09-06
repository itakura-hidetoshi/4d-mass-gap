import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

section PhysicalOneSlabEightColorWilsonMarginal

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
local notation "A" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
    H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "Color" => PeriodicHypercubicEvenEdgeColor

local instance periodicHypercubicEvenSpecialUnitaryPhysicalEightColor_completeSpace :
    CompleteSpace G :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The canonical eight-color physical residual energy.  The color type is the
fixed Wilson eight-color type, so this normalization carries no volume factor. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColorResidualEnergy
    (P : Color → G →L[ℝ] G)
    (x : G) : ℝ :=
  boundedColorNormalizedResidualEnergy P x

/-- Wilson marginal conditional expectations give the exact eight-color
comparison with the literal raw physical one-slab squared defect.  This is the
requested `η E₈ ≲ defect` statement with constant one after retaining the
natural transfer scale `‖T‖²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColor_rawDefect_of_wilsonMarginalCondExp
    (P : Color → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData P A)
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (x : K) :
    eta * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColorResidualEnergy
        H N hN beta hbeta P (x : G) * ‖T‖ ^ 2 ≤
      ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_hcompare_of_wilsonMarginalCondExp
      H N hN beta hbeta P D eta heta0 heta1 x
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColorResidualEnergy,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect] using h

/-- After dividing by the positive physical transfer norm, the same
Wilson-marginal comparison is the dimensionless normalized-transfer defect
estimate `η E₈ ≤ ‖x‖² - ‖Sx‖²`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColor_normalizedDefect_of_wilsonMarginalCondExp
    (P : Color → G →L[ℝ] G)
    (D : WilsonMarginalCondExpComparisonData P A)
    (eta : ℝ)
    (heta0 : 0 ≤ eta)
    (heta1 : eta ≤ 1)
    (x : K) :
    eta * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColorResidualEnergy
        H N hN beta hbeta P (x : G) ≤
      ‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2 := by
  have hraw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColor_rawDefect_of_wilsonMarginalCondExp
      H N hN beta hbeta P D eta heta0 heta1 x
  have hTpos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have hscale :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
      H N hN beta hbeta x
  have hscaleSq :
      ‖T‖ ^ 2 * ‖S (x : G)‖ ^ 2 = ‖T (x : G)‖ ^ 2 := by
    calc
      ‖T‖ ^ 2 * ‖S (x : G)‖ ^ 2 =
          (‖T‖ * ‖S (x : G)‖) ^ 2 := by ring
      _ = ‖T (x : G)‖ ^ 2 := by rw [hscale]
  have hmul :
      ‖T‖ ^ 2 *
          (eta * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColorResidualEnergy
            H N hN beta hbeta P (x : G)) ≤
        ‖T‖ ^ 2 * (‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2) := by
    calc
      ‖T‖ ^ 2 *
          (eta * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColorResidualEnergy
            H N hN beta hbeta P (x : G)) =
        eta * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabEightColorResidualEnergy
            H N hN beta hbeta P (x : G) * ‖T‖ ^ 2 := by ring
      _ ≤ ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 - ‖T (x : G)‖ ^ 2 := hraw
      _ = ‖T‖ ^ 2 * (‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2) := by
        rw [← hscaleSq]
        ring
  exact (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hTpos)).mp hmul

end PhysicalOneSlabEightColorWilsonMarginal

end

end MathlibAnalytic
end MGAP4D
