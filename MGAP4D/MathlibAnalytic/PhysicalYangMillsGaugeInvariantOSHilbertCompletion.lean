import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBilinearForm
import Mathlib.Analysis.InnerProductSpace.Completion

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A reflection-invariant, reflection-positive weak-star state, packaged as the
input from which the Osterwalder--Schrader pre-Hilbert space is generated. -/
structure PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S) where
  omega : WeakDual ℝ
    (physicalYangMillsGaugeInvariantObservableSubalgebra S)
  reflectionInvariant : D.WeakStarReflectionInvariant omega
  reflectionPositive : D.WeakStarReflectionPositive omega

/-- An opaque positive-time gauge-invariant observable, stored over the raw
bounded-continuous carrier.  This avoids inheriting the supremum norm while
retaining exact proofs of gauge invariance and positive-time support. -/
structure PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.Carrier
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    (P : D.OSPreHilbertData) where
  observable : BoundedContinuousFunction S.Configuration ℝ
  gaugeInvariant : observable ∈ physicalYangMillsGaugeInvariantObservableSubalgebra S
  positiveTime :
    (⟨observable, gaugeInvariant⟩ :
      physicalYangMillsGaugeInvariantObservableSubalgebra S) ∈
      D.positiveTimeSubalgebra

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}

/-- Forget only the positive-time proof. -/
def Carrier.toGaugeInvariant
    {P : D.OSPreHilbertData} (F : P.Carrier) :
    physicalYangMillsGaugeInvariantObservableSubalgebra S :=
  ⟨F.observable, F.gaugeInvariant⟩

/-- Regard the opaque carrier as an element of the original positive-time
submodule used by the OS bilinear form. -/
def toPositiveTime (P : D.OSPreHilbertData) (F : P.Carrier) :
    D.positiveTimeSubalgebra.toSubmodule :=
  ⟨F.toGaugeInvariant, F.positiveTime⟩

protected def Carrier.zero (P : D.OSPreHilbertData) : P.Carrier where
  observable := 0
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).zero_mem
  positiveTime := by
    change (0 : physicalYangMillsGaugeInvariantObservableSubalgebra S) ∈
      D.positiveTimeSubalgebra
    exact D.positiveTimeSubalgebra.zero_mem

protected def Carrier.add
    {P : D.OSPreHilbertData} (F G : P.Carrier) : P.Carrier where
  observable := F.observable + G.observable
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).add_mem
      F.gaugeInvariant G.gaugeInvariant
  positiveTime := by
    change F.toGaugeInvariant + G.toGaugeInvariant ∈ D.positiveTimeSubalgebra
    exact D.positiveTimeSubalgebra.add_mem F.positiveTime G.positiveTime

protected def Carrier.neg
    {P : D.OSPreHilbertData} (F : P.Carrier) : P.Carrier where
  observable := -F.observable
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).neg_mem F.gaugeInvariant
  positiveTime := by
    change -F.toGaugeInvariant ∈ D.positiveTimeSubalgebra
    exact neg_mem F.positiveTime

protected def Carrier.sub
    {P : D.OSPreHilbertData} (F G : P.Carrier) : P.Carrier where
  observable := F.observable - G.observable
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).sub_mem
      F.gaugeInvariant G.gaugeInvariant
  positiveTime := by
    change F.toGaugeInvariant - G.toGaugeInvariant ∈ D.positiveTimeSubalgebra
    exact sub_mem F.positiveTime G.positiveTime

protected def Carrier.nsmul
    {P : D.OSPreHilbertData} (n : ℕ) (F : P.Carrier) : P.Carrier where
  observable := n • F.observable
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).nsmul_mem
      F.gaugeInvariant n
  positiveTime := by
    change n • F.toGaugeInvariant ∈ D.positiveTimeSubalgebra
    exact D.positiveTimeSubalgebra.nsmul_mem F.positiveTime n

protected def Carrier.zsmul
    {P : D.OSPreHilbertData} (n : ℤ) (F : P.Carrier) : P.Carrier where
  observable := n • F.observable
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).zsmul_mem
      F.gaugeInvariant n
  positiveTime := by
    change n • F.toGaugeInvariant ∈ D.positiveTimeSubalgebra
    exact zsmul_mem F.positiveTime n

protected def Carrier.smul
    {P : D.OSPreHilbertData} (r : ℝ) (F : P.Carrier) : P.Carrier where
  observable := r • F.observable
  gaugeInvariant :=
    (physicalYangMillsGaugeInvariantObservableSubalgebra S).smul_mem
      F.gaugeInvariant r
  positiveTime := by
    change r • F.toGaugeInvariant ∈ D.positiveTimeSubalgebra
    exact D.positiveTimeSubalgebra.smul_mem F.positiveTime r

theorem Carrier.observable_injective (P : D.OSPreHilbertData) :
    Function.Injective (@Carrier.observable S D P) := by
  intro F G h
  cases F
  cases G
  cases h
  rfl

instance carrierAddCommGroup (P : D.OSPreHilbertData) : AddCommGroup P.Carrier := by
  letI : Zero P.Carrier := ⟨Carrier.zero P⟩
  letI : Add P.Carrier := ⟨Carrier.add⟩
  letI : Neg P.Carrier := ⟨Carrier.neg⟩
  letI : Sub P.Carrier := ⟨Carrier.sub⟩
  letI : SMul ℕ P.Carrier := ⟨Carrier.nsmul⟩
  letI : SMul ℤ P.Carrier := ⟨Carrier.zsmul⟩
  refine Function.Injective.addCommGroup Carrier.observable
    (Carrier.observable_injective P) ?_ ?_ ?_ ?_ ?_ ?_
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

instance carrierRealSMul (P : D.OSPreHilbertData) : SMul ℝ P.Carrier :=
  ⟨Carrier.smul⟩

instance carrierModule (P : D.OSPreHilbertData) : Module ℝ P.Carrier := by
  refine Function.Injective.module ℝ
    ⟨⟨Carrier.observable, ?_⟩, ?_⟩
    (Carrier.observable_injective P) ?_
  · rfl
  · intro F G
    rfl
  · intro r F
    rfl

@[simp] theorem Carrier.observable_zero (P : D.OSPreHilbertData) :
    (0 : P.Carrier).observable = 0 := rfl

@[simp] theorem Carrier.observable_add
    {P : D.OSPreHilbertData} (F G : P.Carrier) :
    (F + G).observable = F.observable + G.observable := rfl

@[simp] theorem Carrier.observable_neg
    {P : D.OSPreHilbertData} (F : P.Carrier) :
    (-F).observable = -F.observable := rfl

@[simp] theorem Carrier.observable_sub
    {P : D.OSPreHilbertData} (F G : P.Carrier) :
    (F - G).observable = F.observable - G.observable := rfl

@[simp] theorem Carrier.observable_nsmul
    {P : D.OSPreHilbertData} (n : ℕ) (F : P.Carrier) :
    (n • F).observable = n • F.observable := rfl

@[simp] theorem Carrier.observable_zsmul
    {P : D.OSPreHilbertData} (n : ℤ) (F : P.Carrier) :
    (n • F).observable = n • F.observable := rfl

@[simp] theorem Carrier.observable_smul
    {P : D.OSPreHilbertData} (r : ℝ) (F : P.Carrier) :
    (r • F).observable = r • F.observable := rfl

@[simp] theorem toPositiveTime_add
    (P : D.OSPreHilbertData) (F G : P.Carrier) :
    P.toPositiveTime (F + G) = P.toPositiveTime F + P.toPositiveTime G := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp] theorem toPositiveTime_smul
    (P : D.OSPreHilbertData) (r : ℝ) (F : P.Carrier) :
    P.toPositiveTime (r • F) = r • P.toPositiveTime F := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The positive semidefinite OS form as a Mathlib pre-inner-product core. -/
@[reducible] noncomputable def core (P : D.OSPreHilbertData) :
    PreInnerProductSpace.Core ℝ P.Carrier where
  inner F G := D.osBilinForm P.omega (P.toPositiveTime F) (P.toPositiveTime G)
  conj_inner_symm F G := by
    change D.osBilinForm P.omega (P.toPositiveTime G) (P.toPositiveTime F) =
      D.osBilinForm P.omega (P.toPositiveTime F) (P.toPositiveTime G)
    exact (D.osBilinForm_isSymm P.omega P.reflectionInvariant).eq
      (P.toPositiveTime G) (P.toPositiveTime F)
  re_inner_nonneg F := by
    change 0 ≤ D.osBilinForm P.omega (P.toPositiveTime F) (P.toPositiveTime F)
    exact (D.osBilinForm_isNonneg P.omega P.reflectionPositive).nonneg
      (P.toPositiveTime F)
  add_left F G H := by
    simp
  smul_left F G r := by
    simp

/-- The OS core induces exactly the seminormed additive structure used in
Mathlib's GNS construction. -/
noncomputable instance carrierSeminormedAddCommGroup
    (P : D.OSPreHilbertData) : SeminormedAddCommGroup P.Carrier :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := P.core)

/-- The same OS core supplies the compatible real inner-product-space
structure. -/
noncomputable instance carrierInnerProductSpace
    (P : D.OSPreHilbertData) : InnerProductSpace ℝ P.Carrier :=
  InnerProductSpace.ofCore P.core

/-- The inner product on the opaque carrier is definitionally the reflected
continuum expectation. -/
@[simp] theorem inner_eq_osBilinForm
    (P : D.OSPreHilbertData) (F G : P.Carrier) :
    inner ℝ F G =
      D.osBilinForm P.omega (P.toPositiveTime F) (P.toPositiveTime G) := by
  rfl

/-- The OS null vectors form a real linear subspace. -/
def nullSubmodule (P : D.OSPreHilbertData) : Submodule ℝ P.Carrier where
  carrier := {F | ‖F‖ = 0}
  zero_mem' := norm_zero
  add_mem' := by
    intro F G hF hG
    apply le_antisymm
    · calc
        ‖F + G‖ ≤ ‖F‖ + ‖G‖ := norm_add_le F G
        _ = 0 := by rw [hF, hG]; simp
    · exact norm_nonneg _
  smul_mem' := by
    intro r F hF
    change ‖r • F‖ = 0
    rw [norm_smul, hF, mul_zero]

@[simp] theorem mem_nullSubmodule
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    F ∈ P.nullSubmodule ↔ ‖F‖ = 0 :=
  Iff.rfl

/-- The OS null condition is exactly vanishing of the reflected quadratic
expectation. -/
theorem mem_nullSubmodule_iff_osQuadratic_eq_zero
    (P : D.OSPreHilbertData) (F : P.Carrier) :
    F ∈ P.nullSubmodule ↔
      D.osBilinForm P.omega (P.toPositiveTime F) (P.toPositiveTime F) = 0 := by
  rw [P.mem_nullSubmodule]
  constructor
  · intro hF
    calc
      D.osBilinForm P.omega (P.toPositiveTime F) (P.toPositiveTime F) =
          inner ℝ F F := by rw [P.inner_eq_osBilinForm]
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
      _ = 0 := by rw [hF]; simp
  · intro hF
    have hsq : ‖F‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq F, P.inner_eq_osBilinForm]
      exact hF
    exact sq_eq_zero_iff.mp hsq

/-- The separated OS pre-Hilbert space.  Mathlib's `SeparationQuotient`
identifies precisely the vectors invisible to the OS seminorm. -/
abbrev Separated (P : D.OSPreHilbertData) : Type :=
  SeparationQuotient P.Carrier

/-- The completed physical OS Hilbert carrier. -/
def PhysicalHilbert (P : D.OSPreHilbertData) : Type :=
  UniformSpace.Completion P.Separated

noncomputable instance physicalHilbertNormedAddCommGroup
    (P : D.OSPreHilbertData) : NormedAddCommGroup P.PhysicalHilbert := by
  change NormedAddCommGroup (UniformSpace.Completion P.Separated)
  exact UniformSpace.Completion.instNormedAddCommGroup P.Separated

noncomputable instance physicalHilbertInnerProductSpace
    (P : D.OSPreHilbertData) : InnerProductSpace ℝ P.PhysicalHilbert := by
  change InnerProductSpace ℝ (UniformSpace.Completion P.Separated)
  exact UniformSpace.Completion.innerProductSpace

noncomputable instance physicalHilbertCompleteSpace
    (P : D.OSPreHilbertData) : CompleteSpace P.PhysicalHilbert := by
  change CompleteSpace (UniformSpace.Completion P.Separated)
  exact UniformSpace.Completion.completeSpace P.Separated

/-- The OS class of a positive-time observable before Hilbert completion. -/
def osClass (P : D.OSPreHilbertData) (F : P.Carrier) : P.Separated :=
  SeparationQuotient.mk F

/-- The dense physical vector represented by a positive-time observable. -/
def physicalState (P : D.OSPreHilbertData) (F : P.Carrier) : P.PhysicalHilbert := by
  change UniformSpace.Completion P.Separated
  exact (P.osClass F : UniformSpace.Completion P.Separated)

/-- The separated OS quotient is dense in the completed physical carrier. -/
theorem separated_dense_in_physical (P : D.OSPreHilbertData) :
    DenseRange
      (fun x : P.Separated =>
        (x : UniformSpace.Completion P.Separated)) :=
  UniformSpace.Completion.denseRange_coe

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- The actual continuum even-periodic Wilson state supplies all data required
for the OS null quotient and Hilbert completion. -/
noncomputable def physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    D.OSPreHilbertData :=
  { omega := physicalYangMillsContinuumGaugeInvariantWeakStarState S
    reflectionInvariant :=
      physical_yang_mills_gaugeInvariantWeakStarReflectionInvariance_passes_to_limit
        S D hInvariant
    reflectionPositive :=
      physical_yang_mills_evenPeriodicWilsonOS_continuum_weakStarReflectionPositive
        S D halfExtent N hN beta hbeta B }

/-- The actual continuum Wilson OS state therefore has a complete real Hilbert
space obtained canonically from positive-time gauge-invariant observables. -/
theorem physical_yang_mills_evenPeriodicWilsonOS_continuum_physicalHilbert_complete
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) :
    CompleteSpace
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant).PhysicalHilbert := by
  infer_instance

end

end MathlibAnalytic
end MGAP4D
