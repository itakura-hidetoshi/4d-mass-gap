import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachFinProductEncodingCore
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- Encode a finite dependent family of Banach-valued observables as one
observable with values in the finite dependent sup-norm product. -/
noncomputable def continuousLinearMapJointRemainderDependentPiProductObservable
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) :
    (V →L[ℝ] V) →L[ℝ] (∀ i, W i) :=
  ContinuousLinearMap.pi φ

@[simp] theorem continuousLinearMapJointRemainderDependentPiProductObservable_apply
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (A : V →L[ℝ] V) (i : ι) :
    continuousLinearMapJointRemainderDependentPiProductObservable φ A i = φ i A := by
  rfl

/-- Coordinate projection recovers the corresponding member of a dependent
finite observable family definitionally. -/
@[simp] theorem continuousLinearMapJointRemainder_proj_comp_dependentPiProductObservable
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι) :
    (ContinuousLinearMap.proj i : (∀ j, W j) →L[ℝ] W i).comp
        (continuousLinearMapJointRemainderDependentPiProductObservable φ) = φ i := by
  ext A
  rfl

/-- Every coordinate projection from a finite dependent sup-norm product is a
contraction. -/
theorem continuousLinearMapJointRemainder_norm_dependentPi_proj_le_one
    {ι : Type*} [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (i : ι) :
    ‖(ContinuousLinearMap.proj i : (∀ j, W j) →L[ℝ] W i)‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (ContinuousLinearMap.proj i : (∀ j, W j) →L[ℝ] W i)
    zero_le_one
    (fun x => by
      simpa using
        ((pi_norm_le_iff_of_nonneg (x := x) (r := ‖x‖) (norm_nonneg x)).1 le_rfl i))

/-- Every dependent coordinate response order is bounded by the response order
of the single Pi-product observable. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_le_dependentPiProductObservable
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        q M epsilon := by
  simpa using
    continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
      (ContinuousLinearMap.proj i : (∀ j, W j) →L[ℝ] W i)
      (continuousLinearMapJointRemainderDependentPiProductObservable φ)
      (continuousLinearMapJointRemainder_norm_dependentPi_proj_le_one i)
      hq0 hq1 hM hepsilon

/-- One natural number packages the carrier, one dependent Pi-product response,
every dependent coordinate response, and trace. -/
noncomputable def continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
    [continuousLinearMapJointRemainderDependentPiProductObservable φ]
    q M epsilon

/-- Exact threshold characterization of the dependent Pi-product master order. -/
theorem continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder_le_iff
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilon : ℝ) (N : ℕ) :
    continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        φ q M epsilon ≤ N ↔
      continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon ≤ N ∧
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        q M epsilon ≤ N ∧
      continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon ≤ N := by
  simpa [continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder] using
    continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_le_iff
      [continuousLinearMapJointRemainderDependentPiProductObservable φ]
      q M epsilon N

/-- The encoded dependent product response order lies below its master order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_master
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        q M epsilon ≤
      continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        φ q M epsilon := by
  exact
    continuousLinearMapJointRemainderResponseSafeOrder_le_finiteResponseFamilyMasterSafeOrder_of_mem
      [continuousLinearMapJointRemainderDependentPiProductObservable φ]
      q M epsilon (by simp)

/-- Every coordinate response order lies below the dependent Pi-product master
order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductMaster
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (i : ι)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M epsilon ≤
      continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        φ q M epsilon := by
  exact le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_le_dependentPiProductObservable
      φ i hq0 hq1 hM hepsilon)
    (continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_le_master
      φ q M epsilon)

/-- The carrier order lies below the dependent Pi-product master order. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_dependentPiProductMaster
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon ≤
      continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        φ q M epsilon := by
  exact
    continuousLinearMapJointRemainderCarrierSharpOrder_le_finiteResponseFamilyMasterSafeOrder
      [continuousLinearMapJointRemainderDependentPiProductObservable φ]
      q M epsilon

/-- The trace order lies below the dependent Pi-product master order. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_dependentPiProductMaster
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon ≤
      continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        φ q M epsilon := by
  exact
    continuousLinearMapJointRemainderTraceSafeOrder_le_finiteResponseFamilyMasterSafeOrder
      [continuousLinearMapJointRemainderDependentPiProductObservable φ]
      q M epsilon

/-- Every base order above the dependent Pi-product master threshold controls
the carrier, encoded dependent product, every coordinate response, and trace at
the same natural order. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_dependentPiProductMasterSafeOrder_le
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder : continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
      φ q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    (∀ i,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have hfamily :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finiteResponseFamilyMasterSafeOrder_le
      [continuousLinearMapJointRemainderDependentPiProductObservable φ]
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon hq0 hq1 hM hperturb hend hbaseOrder hepsilon
  refine ⟨hfamily.1,
    hfamily.2.1
      (continuousLinearMapJointRemainderDependentPiProductObservable φ) (by simp),
    ?_, hfamily.2.2⟩
  intro i
  exact
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
      (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon hq0 hq1 hM hperturb hend
      (le_trans
        (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_dependentPiProductMaster
          φ i hq0 hq1 hM hepsilon)
        hbaseOrder)
      hepsilon

/-- The explicit dependent Pi-product master order gives simultaneous control
without any further order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_dependentPiProductMasterSafeOrder
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)]
    [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    let N := continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
      φ q M epsilon
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    (∀ i,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  dsimp
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_dependentPiProductMasterSafeOrder_le
      φ
      (continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        φ q M epsilon)
      taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon hq0 hq1 hM hperturb hend le_rfl hepsilon

/-- Reindex a homogeneous finite product by an equivalence of its finite
coordinate type. -/
noncomputable def continuousLinearMapJointRemainderFinProductReindexMap
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (e : Fin n ≃ Fin n) :
    (Fin n → W) →L[ℝ] (Fin n → W) :=
  Pi.compRightL ℝ (fun _ : Fin n => W) e

@[simp] theorem continuousLinearMapJointRemainderFinProductReindexMap_apply
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (e : Fin n ≃ Fin n) (x : Fin n → W) (i : Fin n) :
    continuousLinearMapJointRemainderFinProductReindexMap e x i = x (e i) := by
  rfl

/-- Reindexing a homogeneous finite sup-norm product is a contraction. -/
theorem continuousLinearMapJointRemainder_norm_finProductReindexMap_le_one
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (e : Fin n ≃ Fin n) :
    ‖(continuousLinearMapJointRemainderFinProductReindexMap e :
      (Fin n → W) →L[ℝ] (Fin n → W))‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (continuousLinearMapJointRemainderFinProductReindexMap e :
      (Fin n → W) →L[ℝ] (Fin n → W))
    zero_le_one
    (fun x => by
      rw [pi_norm_le_iff_of_nonneg (x :=
        continuousLinearMapJointRemainderFinProductReindexMap e x)
        (r := ‖x‖) (norm_nonneg x)]
      intro i
      simpa using
        ((pi_norm_le_iff_of_nonneg (x := x) (r := ‖x‖) (norm_nonneg x)).1 le_rfl (e i)))

/-- Reindexing the coordinates of a homogeneous Pi-product observable is
postcomposition by the finite-product reindexing contraction. -/
@[simp] theorem continuousLinearMapJointRemainderFinProductReindexMap_comp_observable
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (e : Fin n ≃ Fin n) :
    (continuousLinearMapJointRemainderFinProductReindexMap e).comp
        (continuousLinearMapJointRemainderDependentPiProductObservable
          (W := fun _ : Fin n => W) φ) =
      continuousLinearMapJointRemainderDependentPiProductObservable
        (W := fun _ : Fin n => W) (fun i => φ (e i)) := by
  ext A i
  rfl

/-- Homogeneous finite-product response safe order is invariant under any
permutation of the finite coordinate type. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_reindex_eq
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (e : Fin n ≃ Fin n)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable
          (W := fun _ : Fin n => W) (fun i => φ (e i)))
        q M epsilon =
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable
          (W := fun _ : Fin n => W) φ)
        q M epsilon := by
  apply le_antisymm
  · rw [← continuousLinearMapJointRemainderFinProductReindexMap_comp_observable φ e]
    exact
      continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
        (continuousLinearMapJointRemainderFinProductReindexMap e)
        (continuousLinearMapJointRemainderDependentPiProductObservable
          (W := fun _ : Fin n => W) φ)
        (continuousLinearMapJointRemainder_norm_finProductReindexMap_le_one e)
        hq0 hq1 hM hepsilon
  · have h :=
      continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
        (continuousLinearMapJointRemainderFinProductReindexMap e.symm)
        (continuousLinearMapJointRemainderDependentPiProductObservable
          (W := fun _ : Fin n => W) (fun i => φ (e i)))
        (continuousLinearMapJointRemainder_norm_finProductReindexMap_le_one e.symm)
        hq0 hq1 hM hepsilon
    rw [continuousLinearMapJointRemainderFinProductReindexMap_comp_observable] at h
    simpa using h

/-- The homogeneous dependent Pi-product master order is permutation
invariant. -/
theorem continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder_reindex_eq
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (e : Fin n ≃ Fin n)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        (W := fun _ : Fin n => W) (fun i => φ (e i)) q M epsilon =
      continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
        (W := fun _ : Fin n => W) φ q M epsilon := by
  unfold continuousLinearMapJointRemainderDependentPiProductMasterSafeOrder
  unfold continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
  simp only [continuousLinearMapJointRemainderResponseFamilySafeOrder_singleton]
  rw [continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_reindex_eq
    φ e hq0 hq1 hM hepsilon]

end MathlibAnalytic
end MGAP4D