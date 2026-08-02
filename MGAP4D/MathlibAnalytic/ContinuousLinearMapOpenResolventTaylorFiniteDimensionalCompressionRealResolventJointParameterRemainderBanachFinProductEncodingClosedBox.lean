import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFinProductEncodingCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFiniteResponseFamilyClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The closed-box finite-product master order packages a `Fin n` family as one
sup-norm product observable over an arbitrary joint approximation net. -/
noncomputable def JointRemainderClosedBoxSharpCertificateData.finProductMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions responseCount : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) : ℕ :=
  C.finiteResponseFamilyMasterOrder
    [continuousLinearMapJointRemainderFinProductObservable φ] epsilon

/-- The closed-box encoded-product response order lies below its master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_finProduct_le_master
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions responseCount : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderFinProductObservable φ) epsilon ≤
      C.finProductMasterOrder φ epsilon := by
  exact C.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
    [continuousLinearMapJointRemainderFinProductObservable φ]
    epsilon (by simp)

/-- Every closed-box coordinate response order lies below the finite-product
master order. -/
theorem JointRemainderClosedBoxSharpCertificateData.responseOrder_coord_le_finProductMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions responseCount : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (i : Fin responseCount)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.responseOrder (φ i) epsilon ≤ C.finProductMasterOrder φ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  exact le_trans
    (by
      simpa [JointRemainderClosedBoxSharpCertificateData.responseOrder] using
        continuousLinearMapJointRemainderResponseSafeOrder_le_finProductObservable
          φ i C.hq0 C.hq1 C.hM hhalf)
    (C.responseOrder_finProduct_le_master φ epsilon)

/-- The closed-box master order of the original coordinate list is bounded by
the master order of its single finite-product encoding. -/
theorem JointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder_ofFn_le_finProductMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions responseCount : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.finiteResponseFamilyMasterOrder (List.ofFn φ) epsilon ≤
      C.finProductMasterOrder φ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  simpa [JointRemainderClosedBoxSharpCertificateData.finiteResponseFamilyMasterOrder,
    JointRemainderClosedBoxSharpCertificateData.finProductMasterOrder] using
    continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_ofFn_le_finProductMaster
      φ C.hq0 C.hq1 C.hM hhalf

/-- The closed-box finite-product master order eventually controls the carrier,
the product response, every coordinate response, and trace simultaneously and
uniformly for an arbitrary joint approximation net. -/
theorem JointRemainderClosedBoxSharpCertificateData.eventually_finProductMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions responseCount : ℕ}
    (C : JointRemainderClosedBoxSharpCertificateData
      (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
    (φ : Fin responseCount → ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, C.D.box.Contains p → ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.finProductMasterOrder φ epsilon)
          0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderFinProductObservable φ)
          (C.finProductMasterOrder φ epsilon)
          0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon ∧
      (∀ i,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) (C.finProductMasterOrder φ epsilon)
            0 tailOrder directions
            (C.D.H b) C.D.ds C.D.h
            (closedBoxJointRemainderApproxBaseFamily
              C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
            (closedBoxJointRemainderApproxEndpointFamily
              C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
              p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.finProductMasterOrder φ epsilon)
          0 tailOrder directions
          (C.D.H b) C.D.ds C.D.h
          (closedBoxJointRemainderApproxBaseFamily
            C.D.J C.D.Q (F (C.D.time b)) (C.D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily
            C.D.J C.D.Q directions (F (C.D.time b)) (C.D.degree b)
            p z (C.D.H b) C.D.ds C.D.h)‖ < epsilon := by
  have hproduct := C.eventually_finiteResponseFamilyMaster_norm_lt
    [continuousLinearMapJointRemainderFinProductObservable φ]
    tailOrder epsilon hepsilon
  have hcoords := C.eventually_response_family_norm_lt_of_orders
    (List.ofFn φ) (C.finProductMasterOrder φ epsilon)
    tailOrder epsilon
    (fun θ hθ => by
      have hrange : θ ∈ Set.range φ := (List.mem_ofFn' φ θ).1 hθ
      rcases hrange with ⟨i, rfl⟩
      exact C.responseOrder_coord_le_finProductMaster φ i epsilon hepsilon)
    hepsilon
  filter_upwards [hproduct, hcoords] with b hp hc
  intro p hpbox z hz
  have hp' := hp p hpbox z hz
  refine ⟨hp'.1,
    hp'.2.1 (continuousLinearMapJointRemainderFinProductObservable φ) (by simp),
    ?_, hp'.2.2⟩
  intro i
  exact hc (φ i)
    ((List.mem_ofFn' φ (φ i)).2 ⟨i, rfl⟩)
    p hpbox z hz

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
