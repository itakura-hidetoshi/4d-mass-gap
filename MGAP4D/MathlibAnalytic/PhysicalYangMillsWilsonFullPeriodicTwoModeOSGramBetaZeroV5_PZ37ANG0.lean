import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTwoModeOSGramKernelV5_PZ37ANG
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonBoundaryAnalysisBetaZeroRankOne
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANG0 — original full-periodic Wilson time-one OS moment at beta = 0

The pre-existing exact Wilson theorem makes the completed positive Gram
feature constant in BOTH boundary and open-half configurations at zero
coupling.  For the SAME two-mode time-one observable from ANC through ANF,
the boundary Gram moment therefore becomes its actual open-half Haar mean
multiplied by the original partition-function normalization.

The time-one observable is not replaced by a boundary-independent test
function, and a constant Gram feature alone does NOT imply the observable
has zero open-half Haar mean.  Vanishing is proved only under an explicitly
stated a.e.-vanishing fiber-mean premise, which remains a concrete
model-dependent verification obligation for the physical top-orthogonal
coefficient pair.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANG0_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANG0_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANG0_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANG0_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANG0_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANG0_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- Exact beta-zero specialization of the ORIGINAL time-one Wilson boundary
moment, retaining possible dependence of the original cylinder on the
reflection-fixed boundary. No vanishing of the fiber Haar mean is assumed
or inferred. -/
theorem p4Q2PZ37ANG0_originalTimeOneBoundaryMoment_eq_openHaarMean
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
      H 0 (by norm_num) c0 c1 b =
    Real.sqrt
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) 0
        (by norm_num)).base.partitionFunction⁻¹) *
    (∫ x, p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
      H c0 c1 (b, x)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)) := by
  unfold p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
  simp only [periodicHypercubicEvenBoundaryObservableGramFeature,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_zero,
    integral_const_mul]

/-- Exact beta-zero null-form obstruction.  Only a.e. ZERO open-half Haar
mean, not ordinary L2 nonzeroness or boundary-independence of the Wilson
Gram feature, entails an OS-null cylinder. -/
theorem p4Q2PZ37ANG0_originalTimeOneOSQuadratic_zero_of_openHaarMean_ae_zero
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ)
    (hMean :
      ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2),
        (∫ x, p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
          H c0 c1 (b, x)
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)) = 0) :
    p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
      H 0 (by norm_num) c0 c1 = 0 := by
  rw [p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic_eq_boundaryGramMoment_sq]
  have hZero :
      (fun b => ‖p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
          H 0 (by norm_num) c0 c1 b‖ ^ 2) =ᵐ[
        periodicHypercubicEvenBoundaryHaarMeasure H 2]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hMean] with b hb
    rw [p4Q2PZ37ANG0_originalTimeOneBoundaryMoment_eq_openHaarMean]
    simp [hb]
  exact (integral_congr_ae hZero).trans (by simp)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANG0_originalTimeOneBoundaryMoment_eq_openHaarMean
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANG0_originalTimeOneOSQuadratic_zero_of_openHaarMean_ae_zero
