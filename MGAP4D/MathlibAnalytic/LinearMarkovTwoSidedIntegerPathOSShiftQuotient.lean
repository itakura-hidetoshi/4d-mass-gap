import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSPreHilbert
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSShiftSymmetry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The positive-time shift on the datum-dependent OS carrier. -/
def carrierShiftLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.Carrier →ₗ[ℝ] D.Carrier where
  toFun := fun F => ⟨linearMarkovPositiveTimeShiftAlgHom F.observable⟩
  map_add' := by
    intro F G
    apply D.carrierObservable_injective
    rfl
  map_smul' := by
    intro r F
    apply D.carrierObservable_injective
    rfl

@[simp] theorem carrierShiftLinearMap_observable
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    (D.carrierShiftLinearMap F).observable =
      linearMarkovPositiveTimeShiftAlgHom F.observable :=
  rfl

/-- The carrier shift preserves the pulled-back OS null submodule. -/
theorem carrierShiftLinearMap_mem_null
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier)
    (hF : F ∈ D.carrierNullSubmodule) :
    D.carrierShiftLinearMap F ∈ D.carrierNullSubmodule := by
  rw [D.mem_carrierNullSubmodule_iff] at hF ⊢
  exact linearMarkovPositiveTimeShift_mem_twoSidedIntegerPathOSNull
    D.initial D.transition D.detailedBalance F.observable hF

@[simp] theorem osClass_add
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : D.Carrier) :
    D.osClass (F + G) = D.osClass F + D.osClass G := by
  change SeparationQuotient.mk (F + G) =
    SeparationQuotient.mk F + SeparationQuotient.mk G
  exact SeparationQuotient.mk_add F G

@[simp] theorem osClass_smul
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (r : ℝ) (F : D.Carrier) :
    D.osClass (r • F) = r • D.osClass F := by
  change SeparationQuotient.mk (r • F) =
    r • SeparationQuotient.mk F
  exact SeparationQuotient.mk_smul r F

/-- Inseparable carrier representatives remain equal after applying the positive-time
shift and passing to the separated OS quotient. -/
theorem osClass_carrierShift_eq_of_inseparable
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : D.Carrier)
    (hFG : Inseparable F G) :
    D.osClass (D.carrierShiftLinearMap F) =
      D.osClass (D.carrierShiftLinearMap G) := by
  have hclass : D.osClass F = D.osClass G := by
    change SeparationQuotient.mk F = SeparationQuotient.mk G
    exact SeparationQuotient.mk_eq_mk.mpr hFG
  have hnull : F.observable - G.observable ∈
      linearMarkovTwoSidedIntegerPathOSNull
        D.initial D.transition D.detailedBalance :=
    (D.osClass_eq_osClass_iff F G).mp hclass
  rw [D.osClass_eq_osClass_iff]
  have hshift :=
    linearMarkovPositiveTimeShift_mem_twoSidedIntegerPathOSNull
      D.initial D.transition D.detailedBalance
      (F.observable - G.observable) hnull
  simpa using hshift

/-- The well-defined positive-time shift on the separated temporal OS quotient. -/
noncomputable def separatedShift
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.Separated → D.Separated :=
  SeparationQuotient.lift
    (fun F : D.Carrier => D.osClass (D.carrierShiftLinearMap F))
    (fun F G hFG => D.osClass_carrierShift_eq_of_inseparable F G hFG)

@[simp] theorem separatedShift_osClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    D.separatedShift (D.osClass F) =
      D.osClass (D.carrierShiftLinearMap F) := by
  apply SeparationQuotient.lift_mk

/-- The positive-time shift as a real linear endomorphism of the separated OS
pre-Hilbert space. -/
noncomputable def separatedShiftLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.Separated →ₗ[ℝ] D.Separated where
  toFun := D.separatedShift
  map_add' := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro F
    refine Quotient.inductionOn y ?_
    intro G
    simp only [D.separatedShift_osClass, D.osClass_add]
    rw [map_add]
  map_smul' := by
    intro r x
    refine Quotient.inductionOn x ?_
    intro F
    simp only [D.separatedShift_osClass, D.osClass_smul]
    rw [map_smul]

@[simp] theorem separatedShiftLinearMap_osClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    D.separatedShiftLinearMap (D.osClass F) =
      D.osClass (D.carrierShiftLinearMap F) :=
  D.separatedShift_osClass F

@[simp] theorem separatedShiftLinearMap_observableClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    D.separatedShiftLinearMap (D.observableClass F) =
      D.observableClass (linearMarkovPositiveTimeShiftAlgHom F) := by
  change D.separatedShiftLinearMap
      (D.osClass (D.carrierOfObservable F)) =
    D.osClass (D.carrierOfObservable
      (linearMarkovPositiveTimeShiftAlgHom F))
  rw [D.separatedShiftLinearMap_osClass]
  rfl

/-- The descended positive-time shift is symmetric for the separated temporal OS
inner product. -/
theorem inner_separatedShiftLinearMap_left_eq_right
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x y : D.Separated) :
    inner ℝ (D.separatedShiftLinearMap x) y =
      inner ℝ x (D.separatedShiftLinearMap y) := by
  refine Quotient.inductionOn x ?_
  intro F
  refine Quotient.inductionOn y ?_
  intro G
  rw [D.separatedShiftLinearMap_osClass,
    D.separatedShiftLinearMap_osClass]
  rw [D.separated_inner_osClass_osClass,
    D.separated_inner_osClass_osClass]
  exact linearMarkovTwoSidedIntegerPathOSForm_shift_left_eq_shift_right
    D.initial D.transition D.detailedBalance F.observable G.observable

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
