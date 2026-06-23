import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDenseStateMap
import Mathlib.Analysis.Normed.Operator.Extend

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Positive Euclidean-time translations on the OS observable carrier,
packaged with exactly the algebraic and contractive data required to descend
through the null quotient and extend to the completed physical Hilbert space. -/
structure PositiveTimeContractionSemigroup (P : D.OSPreHilbertData) where
  translate : ℝ≥0 → P.Carrier →ₗ[ℝ] P.Carrier
  translate_zero : ∀ F, translate 0 F = F
  translate_add : ∀ s t F, translate (s + t) F = translate s (translate t F)
  norm_translate_le : ∀ t F, ‖translate t F‖ ≤ ‖F‖
  vacuumObservable_fixed : ∀ t, translate t P.vacuumObservable = P.vacuumObservable

namespace PositiveTimeContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- Contractivity forces positive-time translation to preserve the OS null
space. -/
theorem translate_mem_nullSubmodule
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0)
    {F : P.Carrier} (hF : F ∈ P.nullSubmodule) :
    T.translate t F ∈ P.nullSubmodule := by
  rw [P.mem_nullSubmodule] at hF ⊢
  apply le_antisymm
  · exact (T.norm_translate_le t F).trans_eq hF
  · exact norm_nonneg _

/-- Translation is contractive on represented physical vectors. -/
theorem translated_physicalState_norm_le
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0) (F : P.Carrier) :
    ‖P.physicalState (T.translate t F)‖ ≤ ‖P.physicalState F‖ := by
  simpa using T.norm_translate_le t F

/-- Translation followed by the dense physical-state map. -/
def translatedDenseStateLinearMap
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0) :
    P.Carrier →ₗ[ℝ] P.PhysicalHilbert :=
  P.physicalStateLinearMap.comp (T.translate t)

@[simp] theorem translatedDenseStateLinearMap_apply
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0) (F : P.Carrier) :
    T.translatedDenseStateLinearMap t F =
      P.physicalState (T.translate t F) := by
  rw [translatedDenseStateLinearMap, LinearMap.comp_apply,
    P.physicalStateLinearMap_apply]

/-- The translated dense-state map is bounded by the original dense embedding
with sharp constant one. -/
theorem translatedDenseStateLinearMap_norm_le
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0) (F : P.Carrier) :
    ‖T.translatedDenseStateLinearMap t F‖ ≤
      1 * ‖P.physicalStateLinearMap F‖ := by
  rw [T.translatedDenseStateLinearMap_apply,
    P.physicalStateLinearMap_apply, one_mul]
  exact T.translated_physicalState_norm_le t F

/-- The unique bounded physical time-translation operator obtained by extending
translation from the dense family of represented OS states. -/
noncomputable def physicalOperator
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0) :
    P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert :=
  (T.translatedDenseStateLinearMap t).extendOfNorm P.physicalStateLinearMap

/-- The completed physical operator agrees with observable translation on the
dense represented-state family. -/
theorem physicalOperator_on_physicalState
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0) (F : P.Carrier) :
    T.physicalOperator t (P.physicalState F) =
      P.physicalState (T.translate t F) := by
  rw [← P.physicalStateLinearMap_apply,
    ← T.translatedDenseStateLinearMap_apply]
  exact LinearMap.extendOfNorm_eq
    P.physicalStateLinearMap_denseRange
    ⟨1, T.translatedDenseStateLinearMap_norm_le t⟩ F

/-- Physical positive-time translations are contractions on the completed
Hilbert space. -/
theorem physicalOperator_norm_le
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0)
    (psi : P.PhysicalHilbert) :
    ‖T.physicalOperator t psi‖ ≤ ‖psi‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := T.translatedDenseStateLinearMap t)
    (e := P.physicalStateLinearMap)
    P.physicalStateLinearMap_denseRange 1
    (T.translatedDenseStateLinearMap_norm_le t) psi
  simpa [PositiveTimeContractionSemigroup.physicalOperator] using h

/-- The physical positive-time operator fixes the normalized OS vacuum. -/
theorem physicalOperator_fixes_vacuum
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0) :
    T.physicalOperator t P.vacuum = P.vacuum := by
  calc
    T.physicalOperator t P.vacuum =
        T.physicalOperator t (P.physicalState P.vacuumObservable) := rfl
    _ = P.physicalState (T.translate t P.vacuumObservable) :=
      T.physicalOperator_on_physicalState t P.vacuumObservable
    _ = P.physicalState P.vacuumObservable := by
      rw [T.vacuumObservable_fixed]
    _ = P.vacuum := rfl

/-- Translation is independent of the chosen observable representative of a
physical vector. -/
theorem translate_respects_physical_equivalence
    (T : P.PositiveTimeContractionSemigroup) (t : ℝ≥0)
    {F G : P.Carrier} (hFG : P.physicalState F = P.physicalState G) :
    P.physicalState (T.translate t F) = P.physicalState (T.translate t G) := by
  calc
    P.physicalState (T.translate t F) =
        T.physicalOperator t (P.physicalState F) :=
      (T.physicalOperator_on_physicalState t F).symm
    _ = T.physicalOperator t (P.physicalState G) := by rw [hFG]
    _ = P.physicalState (T.translate t G) :=
      T.physicalOperator_on_physicalState t G

end PositiveTimeContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
