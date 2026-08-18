import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathContinuumOSBilinearForm
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Fixed-slot OS separation and Hilbert completion for the primary scalar continuum law

For each fixed finite set of nonnegative rational Euclidean times, the preceding
same-root construction supplies a symmetric positive-semidefinite OS bilinear
form on bounded-continuous scalar cylinder observables.  This file performs the
standard Mathlib GNS/OS separation for that one fixed slot set:

* package the exact fixed-slot OS data;
* turn the positive-semidefinite bilinear form into a `PreInnerProductSpace.Core`;
* obtain the induced seminorm and real inner-product structure;
* identify the OS null vectors;
* quotient by zero seminorm using `SeparationQuotient`; and
* complete the separated carrier to a real Hilbert space.

This is intentionally local to one finite slot set.  No directed union over
slot sets, time-translation operator, positive-time closedness assertion,
semigroup, Hamiltonian, spectral claim, or mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact data needed to reconstruct the OS Hilbert carrier for one fixed set of
nonnegative rational slots of the same-root primary scalar continuum law. -/
structure PrimaryScalarFixedSlotOSPreHilbertData
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing) where
  slots : Finset ℚ
  slots_nonneg : ∀ q ∈ slots, 0 ≤ q
  latticeSpacing_pos : ∀ n, 0 < latticeSpacing n
  temporalReach_tendsto :
    Filter.Tendsto
      (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
      Filter.atTop Filter.atTop

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {latticeSpacing : ℕ → ℝ}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta latticeSpacing}

/-- Opaque fixed-slot observable carrier.  The wrapper prevents the OS
seminormed structure associated with one continuum law and one slot set from
colliding with the ambient supremum-norm structure of bounded-continuous
functions. -/
structure FixedSlotCarrier
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) where
  observable :
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable
      P.slots

protected def FixedSlotCarrier.zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : P.FixedSlotCarrier where
  observable := 0

protected def FixedSlotCarrier.add
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (F G : P.FixedSlotCarrier) : P.FixedSlotCarrier where
  observable := F.observable + G.observable

protected def FixedSlotCarrier.neg
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (F : P.FixedSlotCarrier) : P.FixedSlotCarrier where
  observable := -F.observable

protected def FixedSlotCarrier.sub
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (F G : P.FixedSlotCarrier) : P.FixedSlotCarrier where
  observable := F.observable - G.observable

protected def FixedSlotCarrier.nsmul
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (n : ℕ) (F : P.FixedSlotCarrier) : P.FixedSlotCarrier where
  observable := n • F.observable

protected def FixedSlotCarrier.zsmul
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (n : ℤ) (F : P.FixedSlotCarrier) : P.FixedSlotCarrier where
  observable := n • F.observable

protected def FixedSlotCarrier.smul
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (r : ℝ) (F : P.FixedSlotCarrier) : P.FixedSlotCarrier where
  observable := r • F.observable

/-- The wrapped observable determines the fixed-slot carrier element exactly. -/
theorem FixedSlotCarrier.observable_injective
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    Function.Injective
      (@FixedSlotCarrier.observable H N hN _ beta hbeta latticeSpacing L P) := by
  intro F G h
  cases F
  cases G
  cases h
  rfl

instance carrierAddCommGroup
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : AddCommGroup P.FixedSlotCarrier := by
  letI : Zero P.FixedSlotCarrier := ⟨FixedSlotCarrier.zero P⟩
  letI : Add P.FixedSlotCarrier := ⟨FixedSlotCarrier.add⟩
  letI : Neg P.FixedSlotCarrier := ⟨FixedSlotCarrier.neg⟩
  letI : Sub P.FixedSlotCarrier := ⟨FixedSlotCarrier.sub⟩
  letI : SMul ℕ P.FixedSlotCarrier := ⟨FixedSlotCarrier.nsmul⟩
  letI : SMul ℤ P.FixedSlotCarrier := ⟨FixedSlotCarrier.zsmul⟩
  refine Function.Injective.addCommGroup FixedSlotCarrier.observable
    (FixedSlotCarrier.observable_injective P) ?_ ?_ ?_ ?_ ?_ ?_
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
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : SMul ℝ P.FixedSlotCarrier :=
  ⟨FixedSlotCarrier.smul⟩

instance carrierModule
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : Module ℝ P.FixedSlotCarrier := by
  refine Function.Injective.module ℝ
    ⟨⟨FixedSlotCarrier.observable, ?_⟩, ?_⟩
    (FixedSlotCarrier.observable_injective P) ?_
  · rfl
  · intro F G
    rfl
  · intro r F
    rfl

@[simp] theorem FixedSlotCarrier.observable_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    (0 : P.FixedSlotCarrier).observable = 0 := rfl

@[simp] theorem FixedSlotCarrier.observable_add
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (F G : P.FixedSlotCarrier) :
    (F + G).observable = F.observable + G.observable := rfl

@[simp] theorem FixedSlotCarrier.observable_neg
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (F : P.FixedSlotCarrier) :
    (-F).observable = -F.observable := rfl

@[simp] theorem FixedSlotCarrier.observable_sub
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (F G : P.FixedSlotCarrier) :
    (F - G).observable = F.observable - G.observable := rfl

@[simp] theorem FixedSlotCarrier.observable_nsmul
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (n : ℕ) (F : P.FixedSlotCarrier) :
    (n • F).observable = n • F.observable := rfl

@[simp] theorem FixedSlotCarrier.observable_zsmul
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (n : ℤ) (F : P.FixedSlotCarrier) :
    (n • F).observable = n • F.observable := rfl

@[simp] theorem FixedSlotCarrier.observable_smul
    {P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L}
    (r : ℝ) (F : P.FixedSlotCarrier) :
    (r • F).observable = r • F.observable := rfl

/-- The positive-semidefinite fixed-slot OS form as a Mathlib pre-inner-product
core. -/
@[reducible] noncomputable def core
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    PreInnerProductSpace.Core ℝ P.FixedSlotCarrier where
  inner F G :=
    L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing P.slots
      F.observable G.observable
  conj_inner_symm F G := by
    change
      L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing P.slots
          G.observable F.observable =
        L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing P.slots
          F.observable G.observable
    exact
      (L.fixedSlotOSBilinForm_isSymm
        H N hN beta hbeta latticeSpacing P.slots).eq G.observable F.observable
  re_inner_nonneg F := by
    change
      0 ≤ L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing P.slots
        F.observable F.observable
    exact
      (L.fixedSlotOSBilinForm_isNonneg
        H N hN beta hbeta latticeSpacing
        P.latticeSpacing_pos P.temporalReach_tendsto
        P.slots P.slots_nonneg).nonneg F.observable
  add_left F G K := by
    simp
  smul_left F G r := by
    simp

/-- The fixed-slot OS core induces its canonical seminormed additive structure. -/
noncomputable instance carrierSeminormedAddCommGroup
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : SeminormedAddCommGroup P.FixedSlotCarrier :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := P.core)

/-- The same core supplies the compatible real inner-product-space structure. -/
noncomputable instance carrierInnerProductSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : InnerProductSpace ℝ P.FixedSlotCarrier :=
  InnerProductSpace.ofCore P.core

/-- The induced inner product is exactly the continuum fixed-slot OS bilinear
form. -/
@[simp] theorem inner_eq_fixedSlotOSBilinForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F G : P.FixedSlotCarrier) :
    inner ℝ F G =
      L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing P.slots
        F.observable G.observable := by
  rfl

/-- Fixed-slot OS null vectors form a real linear subspace. -/
def nullSubmodule
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : Submodule ℝ P.FixedSlotCarrier where
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
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F : P.FixedSlotCarrier) :
    F ∈ P.nullSubmodule ↔ ‖F‖ = 0 :=
  Iff.rfl

/-- The null condition is exactly vanishing of the fixed-slot OS quadratic
form. -/
theorem mem_nullSubmodule_iff_osQuadratic_eq_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F : P.FixedSlotCarrier) :
    F ∈ P.nullSubmodule ↔
      L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing P.slots
        F.observable F.observable = 0 := by
  rw [P.mem_nullSubmodule]
  constructor
  · intro hF
    calc
      L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing P.slots
          F.observable F.observable = inner ℝ F F := by
        rw [P.inner_eq_fixedSlotOSBilinForm]
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
      _ = 0 := by rw [hF]; simp
  · intro hF
    have hsq : ‖F‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq F, P.inner_eq_fixedSlotOSBilinForm]
      exact hF
    exact sq_eq_zero_iff.mp hsq

/-- The separated fixed-slot OS pre-Hilbert carrier. -/
abbrev Separated
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : Type :=
  SeparationQuotient P.FixedSlotCarrier

/-- Hilbert completion of one fixed finite positive rational slot sector. -/
def Hilbert
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : Type :=
  UniformSpace.Completion P.Separated

noncomputable instance hilbertNormedAddCommGroup
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : NormedAddCommGroup P.Hilbert := by
  change NormedAddCommGroup (UniformSpace.Completion P.Separated)
  exact UniformSpace.Completion.instNormedAddCommGroup P.Separated

noncomputable instance hilbertInnerProductSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : InnerProductSpace ℝ P.Hilbert := by
  change InnerProductSpace ℝ (UniformSpace.Completion P.Separated)
  exact UniformSpace.Completion.innerProductSpace

noncomputable instance hilbertCompleteSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : CompleteSpace P.Hilbert := by
  change CompleteSpace (UniformSpace.Completion P.Separated)
  exact UniformSpace.Completion.completeSpace P.Separated

/-- OS equivalence class of a fixed-slot cylinder observable. -/
def osClass
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F : P.FixedSlotCarrier) : P.Separated :=
  SeparationQuotient.mk F

/-- Dense vector in the fixed-slot Hilbert completion represented by a cylinder
observable. -/
def hilbertState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F : P.FixedSlotCarrier) : P.Hilbert := by
  change UniformSpace.Completion P.Separated
  exact (P.osClass F : UniformSpace.Completion P.Separated)

/-- The separated fixed-slot OS quotient is dense in its Hilbert completion. -/
theorem separated_dense_in_hilbert
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    DenseRange
      (fun x : P.Separated =>
        (x : UniformSpace.Completion P.Separated)) :=
  UniformSpace.Completion.denseRange_coe

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
