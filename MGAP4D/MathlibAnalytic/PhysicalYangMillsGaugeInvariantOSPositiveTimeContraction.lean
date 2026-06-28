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
  translate : NNReal → P.Carrier →ₗ[ℝ] P.Carrier
  translate_zero : ∀ F, translate 0 F = F
  translate_add : ∀ s t F, translate (s + t) F = translate s (translate t F)
  norm_translate_le : ∀ t F, ‖translate t F‖ ≤ ‖F‖
  vacuumObservable_fixed : ∀ t, translate t P.vacuumObservable = P.vacuumObservable

/-- The completed positive-time contraction semigroup on the physical Hilbert
space, including its sharp operator-norm bound and normalized vacuum fixed
vector. -/
structure PhysicalSemigroup (P : D.OSPreHilbertData) where
  operator : NNReal → P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ P.PhysicalHilbert
  operator_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  opNorm_le : ∀ t, ‖operator t‖ ≤ 1
  fixes_vacuum : ∀ t, operator t P.vacuum = P.vacuum

namespace PositiveTimeContractionSemigroup

variable {P : D.OSPreHilbertData}

/-- Contractivity forces positive-time translation to preserve the OS null
space. -/
theorem translate_mem_nullSubmodule
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal)
    {F : P.Carrier} (hF : F ∈ P.nullSubmodule) :
    T.translate t F ∈ P.nullSubmodule := by
  rw [P.mem_nullSubmodule] at hF ⊢
  apply le_antisymm
  · exact (T.norm_translate_le t F).trans_eq hF
  · exact norm_nonneg _

/-- Translation is contractive on represented physical vectors. -/
theorem translated_physicalState_norm_le
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) (F : P.Carrier) :
    ‖P.physicalState (T.translate t F)‖ ≤ ‖P.physicalState F‖ := by
  simpa using T.norm_translate_le t F

/-- Translation followed by the dense physical-state map. -/
def translatedDenseStateLinearMap
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) :
    P.Carrier →ₗ[ℝ] P.PhysicalHilbert :=
  P.physicalStateLinearMap.comp (T.translate t)

@[simp] theorem translatedDenseStateLinearMap_apply
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) (F : P.Carrier) :
    T.translatedDenseStateLinearMap t F =
      P.physicalState (T.translate t F) := by
  rw [translatedDenseStateLinearMap, LinearMap.comp_apply,
    P.physicalStateLinearMap_apply]

/-- The translated dense-state map is bounded by the original dense embedding
with sharp constant one. -/
theorem translatedDenseStateLinearMap_norm_le
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) (F : P.Carrier) :
    ‖T.translatedDenseStateLinearMap t F‖ ≤
      1 * ‖P.physicalStateLinearMap F‖ := by
  rw [T.translatedDenseStateLinearMap_apply,
    P.physicalStateLinearMap_apply, one_mul]
  exact T.translated_physicalState_norm_le t F

/-- The unique bounded physical time-translation operator obtained by extending
translation from the dense family of represented OS states. -/
noncomputable def physicalOperator
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) :
    P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert :=
  (T.translatedDenseStateLinearMap t).extendOfNorm P.physicalStateLinearMap

/-- The completed physical operator agrees with observable translation on the
dense represented-state family. -/
theorem physicalOperator_on_physicalState
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) (F : P.Carrier) :
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
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal)
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
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) :
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
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal)
    {F G : P.Carrier} (hFG : P.physicalState F = P.physicalState G) :
    P.physicalState (T.translate t F) = P.physicalState (T.translate t G) := by
  calc
    P.physicalState (T.translate t F) =
        T.physicalOperator t (P.physicalState F) :=
      (T.physicalOperator_on_physicalState t F).symm
    _ = T.physicalOperator t (P.physicalState G) := by rw [hFG]
    _ = P.physicalState (T.translate t G) :=
      T.physicalOperator_on_physicalState t G

/-- At time zero, the completed physical operator acts pointwise as the
identity. -/
theorem physicalOperator_zero_apply
    (T : P.PositiveTimeContractionSemigroup) (psi : P.PhysicalHilbert) :
    T.physicalOperator 0 psi = psi := by
  have hzero :
      T.physicalOperator 0 =
        ContinuousLinearMap.id ℝ P.PhysicalHilbert := by
    refine LinearMap.extendOfNorm_unique
      P.physicalStateLinearMap_denseRange 1
      (T.translatedDenseStateLinearMap_norm_le 0)
      (ContinuousLinearMap.id ℝ P.PhysicalHilbert) ?_
    ext F
    change P.physicalState F = P.physicalState (T.translate 0 F)
    rw [T.translate_zero]
  rw [hzero]
  rfl

/-- The completed physical operators satisfy the additive semigroup law
pointwise on the whole Hilbert space. -/
theorem physicalOperator_add_apply
    (T : P.PositiveTimeContractionSemigroup) (s t : NNReal)
    (psi : P.PhysicalHilbert) :
    T.physicalOperator (s + t) psi =
      T.physicalOperator s (T.physicalOperator t psi) := by
  have hadd :
      T.physicalOperator (s + t) =
        (T.physicalOperator s).comp (T.physicalOperator t) := by
    refine LinearMap.extendOfNorm_unique
      P.physicalStateLinearMap_denseRange 1
      (T.translatedDenseStateLinearMap_norm_le (s + t))
      ((T.physicalOperator s).comp (T.physicalOperator t)) ?_
    ext F
    change T.physicalOperator s
        (T.physicalOperator t (P.physicalState F)) =
      P.physicalState (T.translate (s + t) F)
    rw [T.physicalOperator_on_physicalState t F,
      T.physicalOperator_on_physicalState s (T.translate t F),
      T.translate_add s t F]
  rw [hadd]
  rfl

/-- The time-zero physical operator is the identity continuous linear map. -/
theorem physicalOperator_zero
    (T : P.PositiveTimeContractionSemigroup) :
    T.physicalOperator 0 = ContinuousLinearMap.id ℝ P.PhysicalHilbert := by
  ext psi
  exact T.physicalOperator_zero_apply psi

/-- The completed physical operators satisfy the additive semigroup law as
bundled continuous linear maps. -/
theorem physicalOperator_add
    (T : P.PositiveTimeContractionSemigroup) (s t : NNReal) :
    T.physicalOperator (s + t) =
      (T.physicalOperator s).comp (T.physicalOperator t) := by
  ext psi
  exact T.physicalOperator_add_apply s t psi

/-- Each completed physical time-translation operator has operator norm at
most one. -/
theorem physicalOperator_opNorm_le
    (T : P.PositiveTimeContractionSemigroup) (t : NNReal) :
    ‖T.physicalOperator t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (T.physicalOperator t) zero_le_one ?_
  intro psi
  simpa using T.physicalOperator_norm_le t psi

/-- Canonical completed contraction semigroup generated by the observable-side
positive-time translations. -/
noncomputable def toPhysicalSemigroup
    (T : P.PositiveTimeContractionSemigroup) : P.PhysicalSemigroup where
  operator := T.physicalOperator
  operator_zero := T.physicalOperator_zero
  operator_add := T.physicalOperator_add
  opNorm_le := T.physicalOperator_opNorm_le
  fixes_vacuum := T.physicalOperator_fixes_vacuum

end PositiveTimeContractionSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
