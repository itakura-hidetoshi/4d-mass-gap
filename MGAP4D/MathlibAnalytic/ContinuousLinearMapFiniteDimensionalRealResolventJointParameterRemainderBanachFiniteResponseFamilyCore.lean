import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachMasterCertificateCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The common safe order of a finite list of Banach-valued continuous linear
observables.  The empty family contributes no response constraint. -/
noncomputable def continuousLinearMapJointRemainderResponseFamilySafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (q M epsilon : ℝ) : ℕ :=
  (φs.map fun φ =>
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon).foldr max 0

@[simp] theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_nil
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder
      ([] : List ((V →L[ℝ] V) →L[ℝ] W)) q M epsilon = 0 := by
  rfl

@[simp] theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_cons
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder
      (φ :: φs) q M epsilon =
      max (continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon)
        (continuousLinearMapJointRemainderResponseFamilySafeOrder φs q M epsilon) := by
  rfl

@[simp] theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_singleton
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder
      [φ] q M epsilon =
      continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon := by
  simp

/-- Every member response order lies below the common family response order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_le_familySafeOrder_of_mem
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {φ : (V →L[ℝ] V) →L[ℝ] W}
    {φs : List ((V →L[ℝ] V) →L[ℝ] W)}
    (q M epsilon : ℝ) (hφ : φ ∈ φs) :
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤
      continuousLinearMapJointRemainderResponseFamilySafeOrder φs q M epsilon := by
  induction φs with
  | nil => simp at hφ
  | cons ψ ψs ih =>
      rw [continuousLinearMapJointRemainderResponseFamilySafeOrder_cons]
      rcases List.mem_cons.mp hφ with rfl | hφ
      · exact le_max_left _ _
      · exact le_trans (ih hφ) (le_max_right _ _)

/-- The common family order is characterized exactly by componentwise order
bounds. -/
theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_le_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (q M epsilon : ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder φs q M epsilon ≤ N ↔
      ∀ φ ∈ φs,
        continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤ N := by
  induction φs with
  | nil => simp
  | cons φ φs ih =>
      simp [ih, max_le_iff]

/-- Enlarging the finite response family cannot decrease its common order. -/
theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_mono_of_subset
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {φs ψs : List ((V →L[ℝ] V) →L[ℝ] W)}
    (q M epsilon : ℝ)
    (hsub : ∀ φ, φ ∈ φs → φ ∈ ψs) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder φs q M epsilon ≤
      continuousLinearMapJointRemainderResponseFamilySafeOrder ψs q M epsilon := by
  rw [continuousLinearMapJointRemainderResponseFamilySafeOrder_le_iff]
  intro φ hφ
  exact continuousLinearMapJointRemainderResponseSafeOrder_le_familySafeOrder_of_mem
    q M epsilon (hsub φ hφ)

/-- The family order of a concatenation is the maximum of the two family
orders. -/
theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_append
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs ψs : List ((V →L[ℝ] V) →L[ℝ] W))
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder (φs ++ ψs) q M epsilon =
      max (continuousLinearMapJointRemainderResponseFamilySafeOrder φs q M epsilon)
        (continuousLinearMapJointRemainderResponseFamilySafeOrder ψs q M epsilon) := by
  apply le_antisymm
  · rw [continuousLinearMapJointRemainderResponseFamilySafeOrder_le_iff]
    intro φ hφ
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact le_trans
        (continuousLinearMapJointRemainderResponseSafeOrder_le_familySafeOrder_of_mem
          q M epsilon hφ) (le_max_left _ _)
    · exact le_trans
        (continuousLinearMapJointRemainderResponseSafeOrder_le_familySafeOrder_of_mem
          q M epsilon hφ) (le_max_right _ _)
  · exact max_le
      (continuousLinearMapJointRemainderResponseFamilySafeOrder_mono_of_subset
        q M epsilon (fun φ hφ => List.mem_append_left _ hφ))
      (continuousLinearMapJointRemainderResponseFamilySafeOrder_mono_of_subset
        q M epsilon (fun φ hφ => List.mem_append_right _ hφ))

/-- A finite-family master order simultaneously controls the carrier, every
listed Banach-valued response, and the basis-independent trace. -/
noncomputable def continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (q M epsilon : ℝ) : ℕ :=
  max (continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon)
    (max (continuousLinearMapJointRemainderResponseFamilySafeOrder φs q M epsilon)
      (continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon))

/-- Exact order-theoretic characterization of the finite-family master order. -/
theorem continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_le_iff
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (q M epsilon : ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon ≤ N ↔
      continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon ≤ N ∧
      (∀ φ ∈ φs,
        continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤ N) ∧
      continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon ≤ N := by
  simp [continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder,
    continuousLinearMapJointRemainderResponseFamilySafeOrder_le_iff,
    max_le_iff]

/-- The carrier threshold lies below the finite-family master threshold. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_finiteResponseFamilyMasterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon ≤
      continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon := by
  exact le_max_left _ _

/-- Every listed response threshold lies below the finite-family master
threshold. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_le_finiteResponseFamilyMasterSafeOrder_of_mem
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {φ : (V →L[ℝ] V) →L[ℝ] W}
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (q M epsilon : ℝ)
    (hφ : φ ∈ φs) :
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤
      continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon := by
  exact le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_le_familySafeOrder_of_mem
      q M epsilon hφ)
    (le_trans (le_max_left _ _) (le_max_right _ _))

/-- The trace threshold lies below the finite-family master threshold. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_finiteResponseFamilyMasterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon ≤
      continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon := by
  exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- Every base order above the finite-family master threshold simultaneously
controls the carrier, all listed responses, and trace. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finiteResponseFamilyMasterSafeOrder_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder :
      continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    (∀ φ ∈ φs,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have hcarrier := le_trans
    (continuousLinearMapJointRemainderCarrierSharpOrder_le_finiteResponseFamilyMasterSafeOrder
      φs q M epsilon) hbaseOrder
  have htrace := le_trans
    (continuousLinearMapJointRemainderTraceSafeOrder_le_finiteResponseFamilyMasterSafeOrder
      φs q M epsilon) hbaseOrder
  constructor
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_sharpOrder_le
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
        hq0 hq1 hM hperturb hend hcarrier hepsilon
  constructor
  · intro φ hφ
    exact
      continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
        φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
        hq0 hq1 hM hperturb hend
        (le_trans
          (continuousLinearMapJointRemainderResponseSafeOrder_le_finiteResponseFamilyMasterSafeOrder_of_mem
            φs q M epsilon hφ) hbaseOrder)
        hepsilon
  · exact
      continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJet_norm_lt_of_safeOrder_le
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
        hq0 hq1 hM hperturb hend htrace hepsilon

/-- The explicit finite-family master order gives simultaneous control without
any further order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_finiteResponseFamilyMasterSafeOrder
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    let N := continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
      φs q M epsilon
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    (∀ φ ∈ φs,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  dsimp
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finiteResponseFamilyMasterSafeOrder_le
      φs
      (continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon)
      taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend le_rfl hepsilon

end MathlibAnalytic
end MGAP4D
