import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumVacuum

namespace MGAP4D
namespace MathlibAnalytic

open Function Set

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- The canonical real-linear projection from positive-time observables to the
separated Osterwalder--Schrader pre-Hilbert quotient. -/
def osClassLinearMap (P : D.OSPreHilbertData) :
    P.Carrier →ₗ[ℝ] P.Separated where
  toFun := P.osClass
  map_add' := by
    intro F G
    rfl
  map_smul' := by
    intro r F
    rfl

@[simp] theorem osClassLinearMap_apply
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    P.osClassLinearMap F = P.osClass F :=
  rfl

/-- Every separated OS class has a positive-time observable representative. -/
theorem osClassLinearMap_surjective (P : D.OSPreHilbertData) :
    Function.Surjective P.osClassLinearMap := by
  intro x
  rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
  exact ⟨F, rfl⟩

/-- The represented-state map from positive-time observables to the completed
physical Hilbert space, bundled as a real-linear map. -/
noncomputable def physicalStateLinearMap (P : D.OSPreHilbertData) :
    P.Carrier →ₗ[ℝ] P.PhysicalHilbert := by
  change P.Carrier →ₗ[ℝ] UniformSpace.Completion P.Separated
  exact
    (UniformSpace.Completion.toComplₗᵢ ℝ P.Separated).toLinearMap.comp
      P.osClassLinearMap

@[simp] theorem physicalStateLinearMap_apply
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    P.physicalStateLinearMap F = P.physicalState F :=
  rfl

/-- The kernel of the completed represented-state map is exactly the OS null
submodule. -/
theorem mem_ker_physicalStateLinearMap_iff
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    F ∈ LinearMap.ker P.physicalStateLinearMap ↔ F ∈ P.nullSubmodule := by
  change P.physicalState F = 0 ↔ ‖F‖ = 0
  rw [← norm_eq_zero, P.norm_physicalState]

/-- The constant unit observable is sent to the canonical physical vacuum. -/
@[simp] theorem physicalStateLinearMap_vacuumObservable
    (P : D.OSPreHilbertData) :
    P.physicalStateLinearMap P.vacuumObservable = P.vacuum :=
  rfl

/-- Positive-time observables represent a dense linear family of vectors in
the completed physical OS Hilbert space. -/
theorem physicalStateLinearMap_denseRange (P : D.OSPreHilbertData) :
    DenseRange P.physicalStateLinearMap := by
  intro x
  apply closure_mono ?_ (P.separated_dense_in_physical x)
  rintro y ⟨q, rfl⟩
  rcases SeparationQuotient.surjective_mk q with ⟨F, rfl⟩
  exact ⟨F, rfl⟩

/-- Equivalently, the closure of represented physical states is the whole
physical Hilbert space. -/
theorem closure_range_physicalStateLinearMap
    (P : D.OSPreHilbertData) :
    closure (Set.range P.physicalStateLinearMap) = Set.univ :=
  (denseRange_iff_closure_range.mp P.physicalStateLinearMap_denseRange)

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
