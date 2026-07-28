import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSNull
import Mathlib.Analysis.InnerProductSpace.Completion

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-state detailed-balanced Markov data together with its full two-sided
integer-time temporal Osterwalder--Schrader form. -/
structure LinearMarkovTwoSidedIntegerPathOSPreHilbertData
    (Ω : Type*) [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] where
  initial : PMF Ω
  transition : Ω → PMF Ω
  detailedBalance : LinearMarkovDetailedBalanceReal initial transition

namespace LinearMarkovTwoSidedIntegerPathOSPreHilbertData

variable {Ω : Type*} [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- An opaque copy of the generated positive-time cylinder algebra whose
seminorm and inner product are allowed to depend on the Markov OS datum. -/
structure Carrier
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) where
  observable : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)

def carrierZero
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) : D.Carrier :=
  ⟨0⟩

def carrierAdd
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (F G : D.Carrier) : D.Carrier :=
  ⟨F.observable + G.observable⟩

def carrierNeg
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (F : D.Carrier) : D.Carrier :=
  ⟨-F.observable⟩

def carrierSub
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (F G : D.Carrier) : D.Carrier :=
  ⟨F.observable - G.observable⟩

def carrierNSMul
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (n : ℕ) (F : D.Carrier) : D.Carrier :=
  ⟨n • F.observable⟩

def carrierZSMul
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (n : ℤ) (F : D.Carrier) : D.Carrier :=
  ⟨n • F.observable⟩

def carrierSMul
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (r : ℝ) (F : D.Carrier) : D.Carrier :=
  ⟨r • F.observable⟩

/-- The observable projection is injective because the OS carrier only changes
the geometric structure, not the underlying positive-time observable. -/
theorem carrierObservable_injective
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    Function.Injective (fun F : D.Carrier => F.observable) := by
  intro F G h
  cases F
  cases G
  cases h
  rfl

instance carrierAddCommGroup
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    AddCommGroup D.Carrier := by
  letI : Zero D.Carrier := ⟨carrierZero D⟩
  letI : Add D.Carrier := ⟨carrierAdd⟩
  letI : Neg D.Carrier := ⟨carrierNeg⟩
  letI : Sub D.Carrier := ⟨carrierSub⟩
  letI : SMul ℕ D.Carrier := ⟨carrierNSMul⟩
  letI : SMul ℤ D.Carrier := ⟨carrierZSMul⟩
  refine Function.Injective.addCommGroup
    (fun F : D.Carrier => F.observable)
    (carrierObservable_injective D) ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro F G
    rfl
  · intro F
    rfl
  · intro F G
    rfl
  · intro F n
    rfl
  · intro F n
    rfl

instance carrierRealSMul
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    SMul ℝ D.Carrier :=
  ⟨carrierSMul⟩

instance carrierModule
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    Module ℝ D.Carrier := by
  refine Function.Injective.module ℝ
    ⟨⟨fun F : D.Carrier => F.observable, ?_⟩, ?_⟩
    (carrierObservable_injective D) ?_
  · rfl
  · intro F G
    rfl
  · intro r F
    rfl

@[simp] theorem carrierObservable_zero
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    (0 : D.Carrier).observable = 0 :=
  rfl

@[simp] theorem carrierObservable_add
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (F G : D.Carrier) :
    (F + G).observable = F.observable + G.observable :=
  rfl

@[simp] theorem carrierObservable_neg
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (F : D.Carrier) :
    (-F).observable = -F.observable :=
  rfl

@[simp] theorem carrierObservable_sub
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (F G : D.Carrier) :
    (F - G).observable = F.observable - G.observable :=
  rfl

@[simp] theorem carrierObservable_nsmul
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (n : ℕ) (F : D.Carrier) :
    (n • F).observable = n • F.observable :=
  rfl

@[simp] theorem carrierObservable_zsmul
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (n : ℤ) (F : D.Carrier) :
    (n • F).observable = n • F.observable :=
  rfl

@[simp] theorem carrierObservable_smul
    {D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω}
    (r : ℝ) (F : D.Carrier) :
    (r • F).observable = r • F.observable :=
  rfl

/-- Embed a generated positive-time cylinder observable into the datum-dependent
OS carrier. -/
def carrierOfObservable
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) : D.Carrier :=
  ⟨F⟩

@[simp] theorem carrierObservable_ofObservable
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    (carrierOfObservable D F).observable = F :=
  rfl

/-- The observable projection as a real linear map. -/
def observableLinearMap
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    D.Carrier →ₗ[ℝ]
      linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω) where
  toFun := fun F => F.observable
  map_add' := by
    intro F G
    rfl
  map_smul' := by
    intro r F
    rfl

@[simp] theorem observableLinearMap_apply
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    D.observableLinearMap F = F.observable :=
  rfl

/-- The positive semidefinite full path-space OS form as a Mathlib
pre-inner-product core. -/
@[reducible] noncomputable def core
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    PreInnerProductSpace.Core ℝ D.Carrier where
  inner F G :=
    linearMarkovTwoSidedIntegerPathOSForm
      D.initial D.transition D.detailedBalance F.observable G.observable
  conj_inner_symm F G := by
    change
      linearMarkovTwoSidedIntegerPathOSForm
          D.initial D.transition D.detailedBalance G.observable F.observable =
        linearMarkovTwoSidedIntegerPathOSForm
          D.initial D.transition D.detailedBalance F.observable G.observable
    exact linearMarkovTwoSidedIntegerPathOSForm_symmetric
      D.initial D.transition D.detailedBalance G.observable F.observable
  re_inner_nonneg F := by
    change
      0 ≤ linearMarkovTwoSidedIntegerPathOSForm
        D.initial D.transition D.detailedBalance F.observable F.observable
    exact linearMarkovTwoSidedIntegerPathOSForm_nonneg
      D.initial D.transition D.detailedBalance F.observable
  add_left F G H := by
    simpa using
      linearMarkovTwoSidedIntegerPathOSForm_add_left
        D.initial D.transition D.detailedBalance
          F.observable G.observable H.observable
  smul_left F G r := by
    simpa using
      linearMarkovTwoSidedIntegerPathOSForm_smul_left
        D.initial D.transition D.detailedBalance r F.observable G.observable

/-- The OS core supplies the canonical seminormed additive structure before
separation by null vectors. -/
noncomputable instance carrierSeminormedAddCommGroup
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    SeminormedAddCommGroup D.Carrier :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := D.core)

/-- The same OS core supplies the compatible real pre-inner-product structure. -/
noncomputable instance carrierInnerProductSpace
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    InnerProductSpace ℝ D.Carrier :=
  InnerProductSpace.ofCore D.core

/-- The carrier inner product is exactly the full two-sided path-space OS form. -/
@[simp] theorem inner_eq_OSForm
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : D.Carrier) :
    inner ℝ F G =
      linearMarkovTwoSidedIntegerPathOSForm
        D.initial D.transition D.detailedBalance F.observable G.observable :=
  rfl

/-- The squared OS seminorm is the reflected quadratic form. -/
theorem norm_sq_eq_OSForm
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    ‖F‖ ^ 2 =
      linearMarkovTwoSidedIntegerPathOSForm
        D.initial D.transition D.detailedBalance F.observable F.observable := by
  calc
    ‖F‖ ^ 2 = inner ℝ F F :=
      (real_inner_self_eq_norm_sq F).symm
    _ = linearMarkovTwoSidedIntegerPathOSForm
        D.initial D.transition D.detailedBalance F.observable F.observable :=
      D.inner_eq_OSForm F F

/-- Pull back the already-constructed algebraic OS null submodule to the opaque
OS carrier. -/
def carrierNullSubmodule
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :
    Submodule ℝ D.Carrier :=
  (linearMarkovTwoSidedIntegerPathOSNull
      D.initial D.transition D.detailedBalance).comap D.observableLinearMap

@[simp] theorem mem_carrierNullSubmodule_iff
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    F ∈ D.carrierNullSubmodule ↔
      F.observable ∈ linearMarkovTwoSidedIntegerPathOSNull
        D.initial D.transition D.detailedBalance :=
  Iff.rfl

/-- The seminorm-zero locus is exactly the previously constructed OS null
submodule; no new quotient relation is introduced. -/
theorem norm_eq_zero_iff_mem_carrierNullSubmodule
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    ‖F‖ = 0 ↔ F ∈ D.carrierNullSubmodule := by
  rw [D.mem_carrierNullSubmodule_iff,
    mem_linearMarkovTwoSidedIntegerPathOSNull_iff]
  rw [← D.norm_sq_eq_OSForm F]
  exact sq_eq_zero_iff.symm

/-- The separated temporal OS pre-Hilbert carrier.  Mathlib's separation quotient
identifies exactly the algebraic OS null submodule. -/
abbrev Separated
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω) :=
  SeparationQuotient D.Carrier

/-- The separated OS class of a datum-dependent carrier observable. -/
def osClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) : D.Separated :=
  SeparationQuotient.mk F

/-- The separated OS class of an original generated positive-time observable. -/
def observableClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) : D.Separated :=
  D.osClass (carrierOfObservable D F)

/-- A carrier observable represents zero in the separated quotient exactly when
it belongs to the OS null submodule. -/
@[simp] theorem osClass_eq_zero_iff
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : D.Carrier) :
    D.osClass F = 0 ↔ F ∈ D.carrierNullSubmodule := by
  change SeparationQuotient.mk F = 0 ↔ F ∈ D.carrierNullSubmodule
  rw [SeparationQuotient.mk_eq_zero_iff]
  exact D.norm_eq_zero_iff_mem_carrierNullSubmodule F

/-- An original positive-time cylinder observable represents zero precisely when
it lies in the full path-space OS null submodule. -/
@[simp] theorem observableClass_eq_zero_iff
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    D.observableClass F = 0 ↔
      F ∈ linearMarkovTwoSidedIntegerPathOSNull
        D.initial D.transition D.detailedBalance := by
  change D.osClass (carrierOfObservable D F) = 0 ↔ _
  rw [D.osClass_eq_zero_iff, D.mem_carrierNullSubmodule_iff]
  rfl

/-- Two carrier representatives define the same separated OS vector exactly when
their observable difference is OS null. -/
theorem osClass_eq_osClass_iff
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : D.Carrier) :
    D.osClass F = D.osClass G ↔
      F.observable - G.observable ∈
        linearMarkovTwoSidedIntegerPathOSNull
          D.initial D.transition D.detailedBalance := by
  change SeparationQuotient.mk F = SeparationQuotient.mk G ↔ _
  rw [← sub_eq_zero, ← SeparationQuotient.mk_sub]
  change D.osClass (F - G) = 0 ↔ _
  rw [D.osClass_eq_zero_iff, D.mem_carrierNullSubmodule_iff]
  rfl

/-- Equality of OS classes for original cylinder observables is quotienting by
exactly the previously constructed algebraic null submodule. -/
theorem observableClass_eq_observableClass_iff
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    D.observableClass F = D.observableClass G ↔
      F - G ∈ linearMarkovTwoSidedIntegerPathOSNull
        D.initial D.transition D.detailedBalance := by
  simpa [observableClass, carrierOfObservable] using
    D.osClass_eq_osClass_iff
      (carrierOfObservable D F) (carrierOfObservable D G)

/-- The inner product of separated representative classes is the original full
path-space temporal OS form. -/
@[simp] theorem separated_inner_osClass_osClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : D.Carrier) :
    inner ℝ (D.osClass F) (D.osClass G) =
      linearMarkovTwoSidedIntegerPathOSForm
        D.initial D.transition D.detailedBalance F.observable G.observable := by
  change inner ℝ (SeparationQuotient.mk F) (SeparationQuotient.mk G) = _
  rw [SeparationQuotient.inner_mk_mk]
  exact D.inner_eq_OSForm F G

/-- The inner product of original observable classes is the full path-space
OS form without any representative ambiguity. -/
@[simp] theorem separated_inner_observableClass_observableClass
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (F G : linearMarkovPositiveTimeCylinderSubalgebra (Ω := Ω)) :
    inner ℝ (D.observableClass F) (D.observableClass G) =
      linearMarkovTwoSidedIntegerPathOSForm
        D.initial D.transition D.detailedBalance F G := by
  change inner ℝ
      (D.osClass (carrierOfObservable D F))
      (D.osClass (carrierOfObservable D G)) = _
  simpa using D.separated_inner_osClass_osClass
    (carrierOfObservable D F) (carrierOfObservable D G)

/-- The separated quotient is positive definite: its inner square vanishes only
at the zero class. -/
theorem separated_inner_self_eq_zero_iff
    (D : LinearMarkovTwoSidedIntegerPathOSPreHilbertData Ω)
    (x : D.Separated) :
    inner ℝ x x = 0 ↔ x = 0 := by
  rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]

end LinearMarkovTwoSidedIntegerPathOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
