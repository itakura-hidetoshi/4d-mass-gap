import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachTransportProductCore
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- Encode a finite family of Banach-valued observables as one observable with
values in the finite sup-norm product `Fin n → W`. -/
noncomputable def continuousLinearMapJointRemainderFinProductObservable
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W)) :
    (V →L[ℝ] V) →L[ℝ] (Fin n → W) :=
  ContinuousLinearMap.pi φ

@[simp] theorem continuousLinearMapJointRemainderFinProductObservable_apply
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (A : V →L[ℝ] V) (i : Fin n) :
    continuousLinearMapJointRemainderFinProductObservable φ A i = φ i A := by
  rfl

/-- Coordinate projection recovers the corresponding member of the encoded
finite family definitionally. -/
@[simp] theorem continuousLinearMapJointRemainder_proj_comp_finProductObservable
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W)) (i : Fin n) :
    (ContinuousLinearMap.proj i : (Fin n → W) →L[ℝ] W).comp
        (continuousLinearMapJointRemainderFinProductObservable φ) = φ i := by
  ext A
  rfl

/-- Every coordinate projection from a finite sup-norm product is a
contraction. -/
theorem continuousLinearMapJointRemainder_norm_proj_le_one
    {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (i : Fin n) :
    ‖(ContinuousLinearMap.proj i : (Fin n → W) →L[ℝ] W)‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (ContinuousLinearMap.proj i : (Fin n → W) →L[ℝ] W)
    zero_le_one
    (fun x => by
      simpa using norm_apply_le_norm x i)

/-- The safe order of every coordinate observable is below the safe order of
the single finite-product observable. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_le_finProductObservable
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W)) (i : Fin n)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderFinProductObservable φ)
        q M epsilon := by
  simpa using
    continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
      (ContinuousLinearMap.proj i : (Fin n → W) →L[ℝ] W)
      (continuousLinearMapJointRemainderFinProductObservable φ)
      (continuousLinearMapJointRemainder_norm_proj_le_one i)
      hq0 hq1 hM hepsilon

/-- The common response order of the original `Fin n` family is below the
response order of its single finite-product encoding. -/
theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_ofFn_le_finProductObservable
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder
        (List.ofFn φ) q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderFinProductObservable φ)
        q M epsilon := by
  rw [continuousLinearMapJointRemainderResponseFamilySafeOrder_le_iff]
  rw [List.forall_mem_ofFn_iff]
  intro i
  exact continuousLinearMapJointRemainderResponseSafeOrder_le_finProductObservable
    φ i hq0 hq1 hM hepsilon

/-- One natural number packages the carrier, the finite-product response, all
coordinate responses, and trace. -/
noncomputable def continuousLinearMapJointRemainderFinProductMasterSafeOrder
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (q M epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
    [continuousLinearMapJointRemainderFinProductObservable φ]
    q M epsilon

/-- The encoded product response order lies below the finite-product master
order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_finProduct_le_master
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderFinProductObservable φ)
        q M epsilon ≤
      continuousLinearMapJointRemainderFinProductMasterSafeOrder
        φ q M epsilon := by
  exact
    continuousLinearMapJointRemainderResponseSafeOrder_le_finiteResponseFamilyMasterSafeOrder_of_mem
      [continuousLinearMapJointRemainderFinProductObservable φ]
      q M epsilon (by simp)

/-- Every coordinate response order lies below the finite-product master
order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_coord_le_finProductMaster
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W)) (i : Fin n)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ i) q M epsilon ≤
      continuousLinearMapJointRemainderFinProductMasterSafeOrder
        φ q M epsilon := by
  exact le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_le_finProductObservable
      φ i hq0 hq1 hM hepsilon)
    (continuousLinearMapJointRemainderResponseSafeOrder_finProduct_le_master
      φ q M epsilon)

/-- The carrier order lies below the finite-product master order. -/
theorem continuousLinearMapJointRemainderCarrierSharpOrder_le_finProductMaster
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderCarrierSharpOrder q M epsilon ≤
      continuousLinearMapJointRemainderFinProductMasterSafeOrder
        φ q M epsilon := by
  exact
    continuousLinearMapJointRemainderCarrierSharpOrder_le_finiteResponseFamilyMasterSafeOrder
      [continuousLinearMapJointRemainderFinProductObservable φ]
      q M epsilon

/-- The trace order lies below the finite-product master order. -/
theorem continuousLinearMapJointRemainderTraceSafeOrder_le_finProductMaster
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderTraceSafeOrder V q M epsilon ≤
      continuousLinearMapJointRemainderFinProductMasterSafeOrder
        φ q M epsilon := by
  exact
    continuousLinearMapJointRemainderTraceSafeOrder_le_finiteResponseFamilyMasterSafeOrder
      [continuousLinearMapJointRemainderFinProductObservable φ]
      q M epsilon

/-- The finite-family master order of the original coordinates is bounded by
the master order of their single product encoding. -/
theorem continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_ofFn_le_finProductMaster
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        (List.ofFn φ) q M epsilon ≤
      continuousLinearMapJointRemainderFinProductMasterSafeOrder
        φ q M epsilon := by
  unfold continuousLinearMapJointRemainderFinProductMasterSafeOrder
  unfold continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
  rw [continuousLinearMapJointRemainderResponseFamilySafeOrder_singleton]
  exact max_le_max le_rfl
    (max_le_max
      (continuousLinearMapJointRemainderResponseFamilySafeOrder_ofFn_le_finProductObservable
        φ hq0 hq1 hM hepsilon)
      le_rfl)

/-- Every base order above the finite-product master threshold controls the
carrier, encoded product response, every coordinate response, and trace at the
same natural order. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finProductMasterSafeOrder_le
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder : continuousLinearMapJointRemainderFinProductMasterSafeOrder
      φ q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (continuousLinearMapJointRemainderFinProductObservable φ)
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    (∀ i,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have hfamily :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finiteResponseFamilyMasterSafeOrder_le
      [continuousLinearMapJointRemainderFinProductObservable φ]
      baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon hq0 hq1 hM hperturb hend hbaseOrder hepsilon
  refine ⟨hfamily.1,
    hfamily.2.1 (continuousLinearMapJointRemainderFinProductObservable φ) (by simp),
    ?_, hfamily.2.2⟩
  intro i
  exact
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
      (φ i) baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon hq0 hq1 hM hperturb hend
      (le_trans
        (continuousLinearMapJointRemainderResponseSafeOrder_coord_le_finProductMaster
          φ i hq0 hq1 hM hepsilon)
        hbaseOrder)
      hepsilon

/-- The explicit finite-product master order gives simultaneous control with no
further order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_finProductMasterSafeOrder
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    let N := continuousLinearMapJointRemainderFinProductMasterSafeOrder
      φ q M epsilon
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (continuousLinearMapJointRemainderFinProductObservable φ)
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    (∀ i,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (φ i) N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  dsimp
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finProductMasterSafeOrder_le
      φ
      (continuousLinearMapJointRemainderFinProductMasterSafeOrder φ q M epsilon)
      taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend le_rfl hepsilon

end MathlibAnalytic
end MGAP4D
