import MGAP4D.MathlibAnalytic.FiniteWilsonOSShiftedKernelSemigroupComparison
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct

noncomputable section

local instance shiftedGeometricOSFinalNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance shiftedGeometricOSFinalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance shiftedGeometricOSFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance shiftedGeometricOSFinalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance shiftedGeometricOSFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance shiftedGeometricOSFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace FiniteWilsonOSReflectionPositivityCertificate
namespace OneLayerShiftedKernelCertificate

variable {L : FiniteLatticeWilsonSystem}
  {P : FiniteWilsonOSReflectionPositivityCertificate L}

/-- Exact bridge defect between the completed shifted geometric Wilson OS
operator and the canonical beta-zero boundary heat-bath step. -/
noncomputable def shiftedKernelHeatBathDefectL2
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N →L[ℝ]
      P.OneLayerHilbert :=
  periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2
    H N hN a boundaryToGeometricOS C.hilbertShiftContinuousLinearMap

/-- Defect zero is exactly one-step intertwining through the explicit isometric
bridge. -/
theorem shiftedKernelHeatBathDefectL2_eq_zero_iff
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    C.shiftedKernelHeatBathDefectL2 H N hN a boundaryToGeometricOS = 0 ↔
      ∀ f : PeriodicHypercubicEvenBoundaryHaarL2 H N,
        C.hilbertShiftContinuousLinearMap (boundaryToGeometricOS f) =
          boundaryToGeometricOS
            (periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
              H N hN 0 le_rfl a f) := by
  exact
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransferHeatBathDefectL2_eq_zero_iff
      H N hN a boundaryToGeometricOS C.hilbertShiftContinuousLinearMap

/-- A zero bridge defect identifies every natural operator power with the
sampled canonical beta-zero heat-bath evolution. -/
theorem hilbertShift_pow_analysis_apply_of_heatBathDefect_eq_zero
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (hD : C.shiftedKernelHeatBathDefectL2
      H N hN a boundaryToGeometricOS = 0)
    (n : ℕ)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    (C.hilbertShiftContinuousLinearMap ^ n) (boundaryToGeometricOS f) =
      boundaryToGeometricOS
        (periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
          H N hN a n f) := by
  exact
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransfer_pow_analysis_apply_of_defect_eq_zero
      H N hN a boundaryToGeometricOS C.hilbertShiftContinuousLinearMap hD n f

/-- Under zero defect, every adjoint compression of a shifted geometric OS
power is exactly the sampled beta-zero heat-bath operator. -/
theorem hilbertShift_compression_pow_eq_sampled_of_heatBathDefect_eq_zero
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (hD : C.shiftedKernelHeatBathDefectL2
      H N hN a boundaryToGeometricOS = 0)
    (n : ℕ) :
    realHilbertIsometricAdjointCompression boundaryToGeometricOS
        (C.hilbertShiftContinuousLinearMap ^ n) =
      periodicHypercubicEvenCanonicalBoundaryBetaZeroSampledHeatBathEvolutionL2
        H N hN a n := by
  exact
    periodicHypercubicEvenCanonicalBoundaryBetaZeroOSTransfer_compression_pow_eq_sampled_of_defect_eq_zero
      H N hN a boundaryToGeometricOS C.hilbertShiftContinuousLinearMap hD n

/-- Simultaneous realization predicate for three layers:

1. the independent shifted kernel;
2. the original unshifted Wilson reflection form;
3. the canonical beta-zero boundary heat-bath step.
-/
def ShiftedKernelReflectionHeatBathRealization
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) : Prop :=
  (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
    finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G =
      P.reflectionData.wilsonOneLayerTransferForm F G) ∧
  C.shiftedKernelHeatBathDefectL2
    H N hN a boundaryToGeometricOS = 0

/-- Exact classification of simultaneous realization.  If the independent
shifted form is also the original OS inner product, its completed operator is
forced to be identity; the heat-bath bridge can then vanish only when the
sampled heat-bath step is identity. -/
theorem shiftedKernelReflectionHeatBathRealization_iff
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    C.ShiftedKernelReflectionHeatBathRealization
        H N hN a boundaryToGeometricOS ↔
      C.hilbertShiftContinuousLinearMap = P.oneLayerIdentityTransfer ∧
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a = 1 := by
  constructor
  · rintro ⟨hReflection, hBridge⟩
    have hOperator :=
      (C.shiftedKernelForm_eq_unshiftedReflectionForm_iff).mp hReflection
    refine ⟨hOperator, ?_⟩
    have hIdentityDefect :
        periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
          P H N hN a boundaryToGeometricOS = 0 := by
      rw [periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2]
      rw [← hOperator]
      exact hBridge
    exact
      (periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff
        P H N hN a boundaryToGeometricOS).mp hIdentityDefect
  · rintro ⟨hOperator, hHeatBath⟩
    constructor
    · exact
        (C.shiftedKernelForm_eq_unshiftedReflectionForm_iff).2 hOperator
    · have hIdentityDefect :
          periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2
            P H N hN a boundaryToGeometricOS = 0 :=
        (periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2_eq_zero_iff
          P H N hN a boundaryToGeometricOS).2 hHeatBath
      rw [periodicHypercubicEvenCanonicalBoundaryBetaZeroGeometricOSIdentityDefectL2]
        at hIdentityDefect
      unfold shiftedKernelHeatBathDefectL2
      rw [hOperator]
      exact hIdentityDefect

/-- A genuinely nonidentity beta-zero heat-bath step rules out simultaneous
realization of the shifted kernel with the unshifted reflection form. -/
theorem shiftedKernelReflectionHeatBathRealization_no_go
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert)
    (hHeatBath :
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a ≠ 1) :
    ¬ C.ShiftedKernelReflectionHeatBathRealization
        H N hN a boundaryToGeometricOS := by
  intro hRealization
  apply hHeatBath
  exact
    (C.shiftedKernelReflectionHeatBathRealization_iff
      H N hN a boundaryToGeometricOS).mp hRealization |>.2

/-- Terminal trichotomy.  For every independent shifted kernel certificate and
explicit boundary bridge, either the shifted kernel differs from the original
reflection form on a concrete observable pair, or the sampled heat-bath step is
identity, or the cross-carrier bridge defect is nonzero. -/
theorem shiftedKernelReflectionHeatBath_terminal_trichotomy
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    (∃ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G ≠
        P.reflectionData.wilsonOneLayerTransferForm F G) ∨
    periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a = 1 ∨
    C.shiftedKernelHeatBathDefectL2
        H N hN a boundaryToGeometricOS ≠ 0 := by
  classical
  by_cases hOperator :
      C.hilbertShiftContinuousLinearMap = P.oneLayerIdentityTransfer
  · by_cases hHeatBath :
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a = 1
    · exact Or.inr (Or.inl hHeatBath)
    · right
      right
      intro hDefect
      apply hHeatBath
      have hReflection :=
        (C.shiftedKernelForm_eq_unshiftedReflectionForm_iff).2 hOperator
      exact
        (C.shiftedKernelReflectionHeatBathRealization_iff
          H N hN a boundaryToGeometricOS).mp
          ⟨hReflection, hDefect⟩ |>.2
  · left
    exact C.exists_shiftedKernelForm_ne_unshifted_of_operator_ne_identity hOperator

/-- Public terminal shifted geometric OS package. -/
theorem physicalYangMillsGaugeInvariantShiftedGeometricOSKernelOperatorFinalPackage
    (C : P.OneLayerShiftedKernelCertificate)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (a : ℝ)
    (boundaryToGeometricOS :
      PeriodicHypercubicEvenBoundaryHaarL2 H N →ₗᵢ[ℝ]
        P.OneLayerHilbert) :
    (∀ x : P.OneLayerHilbert,
      ‖C.hilbertShiftContinuousLinearMap x‖ ≤ ‖x‖) ∧
    (∀ x y : P.OneLayerHilbert,
      inner ℝ (C.hilbertShiftContinuousLinearMap x) y =
        inner ℝ x (C.hilbertShiftContinuousLinearMap y)) ∧
    (∀ x : P.OneLayerHilbert,
      0 ≤ inner ℝ (C.hilbertShiftContinuousLinearMap x) x) ∧
    (∀ m n : ℕ,
      C.hilbertShiftSemigroup (m + n) =
        (C.hilbertShiftSemigroup m).comp
          (C.hilbertShiftSemigroup n)) ∧
    (C.ShiftedKernelReflectionHeatBathRealization
        H N hN a boundaryToGeometricOS ↔
      C.hilbertShiftContinuousLinearMap = P.oneLayerIdentityTransfer ∧
      periodicHypercubicEvenCanonicalBoundaryFullHeatBathEvolutionRealL2
        H N hN 0 le_rfl a = 1) := by
  exact ⟨C.norm_hilbertShiftContinuousLinearMap_le,
    C.inner_hilbertShiftContinuousLinearMap_left_eq_right,
    C.hilbertShiftContinuousLinearMap_quadratic_nonneg,
    C.hilbertShiftSemigroup_add,
    C.shiftedKernelReflectionHeatBathRealization_iff
      H N hN a boundaryToGeometricOS⟩

end OneLayerShiftedKernelCertificate
end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
