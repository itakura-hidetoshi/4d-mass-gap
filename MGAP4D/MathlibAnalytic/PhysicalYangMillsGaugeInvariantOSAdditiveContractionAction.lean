import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingReflectedQuadraticGap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

/-- For a normalized OS state, carrier vacuum centering obeys the exact
Pythagorean norm identity inherited from the completed real Hilbert space. -/
theorem vacuumCenteredCarrier_norm_sq
    (P : D.OSPreHilbertData) (hP : P.IsNormalized) (F : P.Carrier) :
    ‖P.vacuumCenteredCarrier F‖ ^ 2 =
      ‖F‖ ^ 2 - (P.omega F.toGaugeInvariant) ^ 2 := by
  calc
    ‖P.vacuumCenteredCarrier F‖ ^ 2 =
        ‖P.physicalState (P.vacuumCenteredCarrier F)‖ ^ 2 := by
      rw [P.norm_physicalState]
    _ = ‖finiteVacuumCentered P.vacuum (P.physicalState F)‖ ^ 2 := by
      rw [P.physicalState_vacuumCenteredCarrier]
    _ = ‖P.physicalState F‖ ^ 2 -
        (inner ℝ P.vacuum (P.physicalState F)) ^ 2 := by
      exact finite_vacuum_centered_norm_sq
        P.PhysicalHilbert P.vacuum (P.norm_vacuum hP) (P.physicalState F)
    _ = ‖F‖ ^ 2 - (P.omega F.toGaugeInvariant) ^ 2 := by
      rw [P.norm_physicalState, P.inner_vacuum_physicalState]

/-- Contraction action of an arbitrary additive time/index monoid on an OS
carrier.  The index is intentionally abstract: both `NNReal` time and genuine
finite-lattice `ℕ` time can use the same quotient/completion machinery. -/
structure AdditiveContractionAction
    (I : Type*) [AddMonoid I] (P : D.OSPreHilbertData) where
  translate : I → P.Carrier →ₗ[ℝ] P.Carrier
  translate_zero : ∀ F, translate 0 F = F
  translate_add : ∀ s t F, translate (s + t) F = translate s (translate t F)
  norm_translate_le : ∀ i F, ‖translate i F‖ ≤ ‖F‖
  vacuumObservable_fixed : ∀ i, translate i P.vacuumObservable = P.vacuumObservable

namespace AdditiveContractionAction

variable {I : Type*} [AddMonoid I]

/-- Contractivity preserves the OS null space for every index. -/
theorem translate_mem_nullSubmodule
    (A : P.AdditiveContractionAction I) (i : I)
    {F : P.Carrier} (hF : F ∈ P.nullSubmodule) :
    A.translate i F ∈ P.nullSubmodule := by
  rw [P.mem_nullSubmodule] at hF ⊢
  apply le_antisymm
  · exact (A.norm_translate_le i F).trans_eq hF
  · exact norm_nonneg _

/-- Indexed translation followed by the dense represented-state embedding. -/
def translatedDenseStateLinearMap
    (A : P.AdditiveContractionAction I) (i : I) :
    P.Carrier →ₗ[ℝ] P.PhysicalHilbert :=
  P.physicalStateLinearMap.comp (A.translate i)

@[simp] theorem translatedDenseStateLinearMap_apply
    (A : P.AdditiveContractionAction I) (i : I) (F : P.Carrier) :
    A.translatedDenseStateLinearMap i F =
      P.physicalState (A.translate i F) := by
  rw [translatedDenseStateLinearMap, LinearMap.comp_apply,
    P.physicalStateLinearMap_apply]

/-- The dense indexed action has sharp extension constant one. -/
theorem translatedDenseStateLinearMap_norm_le
    (A : P.AdditiveContractionAction I) (i : I) (F : P.Carrier) :
    ‖A.translatedDenseStateLinearMap i F‖ ≤
      1 * ‖P.physicalStateLinearMap F‖ := by
  rw [A.translatedDenseStateLinearMap_apply,
    P.physicalStateLinearMap_apply, P.norm_physicalState, one_mul]
  exact A.norm_translate_le i F

/-- Unique bounded extension of the indexed carrier action to the complete OS
physical Hilbert space. -/
noncomputable def physicalOperator
    (A : P.AdditiveContractionAction I) (i : I) :
    P.PhysicalHilbert →L[ℝ] P.PhysicalHilbert :=
  (A.translatedDenseStateLinearMap i).extendOfNorm P.physicalStateLinearMap

/-- The completed action agrees exactly with carrier translation on represented
physical states. -/
theorem physicalOperator_on_physicalState
    (A : P.AdditiveContractionAction I) (i : I) (F : P.Carrier) :
    A.physicalOperator i (P.physicalState F) =
      P.physicalState (A.translate i F) := by
  rw [← P.physicalStateLinearMap_apply,
    ← A.translatedDenseStateLinearMap_apply]
  exact LinearMap.extendOfNorm_eq
    P.physicalStateLinearMap_denseRange
    ⟨1, A.translatedDenseStateLinearMap_norm_le i⟩ F

/-- Every completed indexed operator is a contraction. -/
theorem physicalOperator_norm_le
    (A : P.AdditiveContractionAction I) (i : I)
    (psi : P.PhysicalHilbert) :
    ‖A.physicalOperator i psi‖ ≤ ‖psi‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := A.translatedDenseStateLinearMap i)
    (e := P.physicalStateLinearMap)
    P.physicalStateLinearMap_denseRange 1
    (A.translatedDenseStateLinearMap_norm_le i) psi
  simpa [AdditiveContractionAction.physicalOperator] using h

/-- The normalized vacuum is fixed by every completed indexed operator. -/
theorem physicalOperator_fixes_vacuum
    (A : P.AdditiveContractionAction I) (i : I) :
    A.physicalOperator i P.vacuum = P.vacuum := by
  calc
    A.physicalOperator i P.vacuum =
        A.physicalOperator i (P.physicalState P.vacuumObservable) := rfl
    _ = P.physicalState (A.translate i P.vacuumObservable) :=
      A.physicalOperator_on_physicalState i P.vacuumObservable
    _ = P.physicalState P.vacuumObservable := by
      rw [A.vacuumObservable_fixed]
    _ = P.vacuum := rfl

/-- The zero index extends to the identity on the whole physical Hilbert
space. -/
theorem physicalOperator_zero_apply
    (A : P.AdditiveContractionAction I) (psi : P.PhysicalHilbert) :
    A.physicalOperator 0 psi = psi := by
  have hzero :
      A.physicalOperator 0 =
        ContinuousLinearMap.id ℝ P.PhysicalHilbert := by
    refine LinearMap.extendOfNorm_unique
      P.physicalStateLinearMap_denseRange 1
      (A.translatedDenseStateLinearMap_norm_le 0)
      (ContinuousLinearMap.id ℝ P.PhysicalHilbert) ?_
    ext F
    change P.physicalState F = P.physicalState (A.translate 0 F)
    rw [A.translate_zero]
  rw [hzero]
  rfl

/-- Additivity of the carrier action extends to the complete physical Hilbert
space. -/
theorem physicalOperator_add_apply
    (A : P.AdditiveContractionAction I) (s t : I)
    (psi : P.PhysicalHilbert) :
    A.physicalOperator (s + t) psi =
      A.physicalOperator s (A.physicalOperator t psi) := by
  have hadd :
      A.physicalOperator (s + t) =
        (A.physicalOperator s).comp (A.physicalOperator t) := by
    refine LinearMap.extendOfNorm_unique
      P.physicalStateLinearMap_denseRange 1
      (A.translatedDenseStateLinearMap_norm_le (s + t))
      ((A.physicalOperator s).comp (A.physicalOperator t)) ?_
    ext F
    change A.physicalOperator s
        (A.physicalOperator t (P.physicalState F)) =
      P.physicalState (A.translate (s + t) F)
    rw [A.physicalOperator_on_physicalState t F,
      A.physicalOperator_on_physicalState s (A.translate t F),
      A.translate_add s t F]
  rw [hadd]
  rfl

/-- Operator norm bound for every completed indexed action. -/
theorem physicalOperator_opNorm_le
    (A : P.AdditiveContractionAction I) (i : I) :
    ‖A.physicalOperator i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (A.physicalOperator i) zero_le_one ?_
  intro psi
  simpa using A.physicalOperator_norm_le i psi

/-- A strict norm estimate on the dense vacuum-centered represented family
extends to the whole vacuum-orthogonal physical sector. -/
theorem physicalOperator_norm_decay_of_centered_core
    (A : P.AdditiveContractionAction I)
    (hP : P.IsNormalized)
    (i : I) (r : ℝ)
    (hCore : ∀ F : P.Carrier,
      ‖A.physicalOperator i
          (finiteVacuumCentered P.vacuum (P.physicalState F))‖ ≤
        r * ‖finiteVacuumCentered P.vacuum (P.physicalState F)‖)
    (phi : P.PhysicalHilbert)
    (hphi : inner ℝ phi P.vacuum = 0) :
    ‖A.physicalOperator i phi‖ ≤ r * ‖phi‖ := by
  have hAll :
      ∀ x : P.PhysicalHilbert,
        ‖A.physicalOperator i
            (finiteVacuumCentered P.vacuum x)‖ ≤
          r * ‖finiteVacuumCentered P.vacuum x‖ := by
    intro x
    refine P.physicalStateLinearMap_denseRange.induction_on x ?_ ?_
    · apply isClosed_le
      · unfold finiteVacuumCentered
        fun_prop
      · unfold finiteVacuumCentered
        fun_prop
    · intro F
      simpa only [P.physicalStateLinearMap_apply] using hCore F
  have hvac : inner ℝ P.vacuum phi = 0 := by
    rw [real_inner_comm]
    exact hphi
  simpa [finiteVacuumCentered, hvac] using hAll phi

end AdditiveContractionAction
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
