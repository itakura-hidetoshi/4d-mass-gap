import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachFinProductEncodingCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachFiniteResponseFamilyCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The compact finite-product master order packages a `Fin n` family as one
sup-norm product observable. -/
noncomputable def JointRemainderCompactSharpCertificateData.finProductMasterOrder
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions n : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) : ℕ :=
  C.finiteResponseFamilyMasterOrder
    [continuousLinearMapJointRemainderFinProductObservable φ] epsilon

/-- The compact encoded-product response order lies below its master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_finProduct_le_master
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions n : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) :
    C.responseOrder
        (continuousLinearMapJointRemainderFinProductObservable φ) epsilon ≤
      C.finProductMasterOrder φ epsilon := by
  exact C.responseOrder_le_finiteResponseFamilyMasterOrder_of_mem
    [continuousLinearMapJointRemainderFinProductObservable φ]
    epsilon (by simp)

/-- Every compact coordinate response order lies below the finite-product
master order. -/
theorem JointRemainderCompactSharpCertificateData.responseOrder_coord_le_finProductMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions n : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W)) (i : Fin n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.responseOrder (φ i) epsilon ≤ C.finProductMasterOrder φ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  exact le_trans
    (by
      simpa [JointRemainderCompactSharpCertificateData.responseOrder] using
        continuousLinearMapJointRemainderResponseSafeOrder_le_finProductObservable
          φ i C.hq0 C.hq1 C.hM hhalf)
    (C.responseOrder_finProduct_le_master φ epsilon)

/-- The compact master order of the original coordinate list is bounded by the
master order of its single finite-product encoding. -/
theorem JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder_ofFn_le_finProductMaster
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions n : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    C.finiteResponseFamilyMasterOrder (List.ofFn φ) epsilon ≤
      C.finProductMasterOrder φ epsilon := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  simpa [JointRemainderCompactSharpCertificateData.finiteResponseFamilyMasterOrder,
    JointRemainderCompactSharpCertificateData.finProductMasterOrder] using
    continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_ofFn_le_finProductMaster
      φ C.hq0 C.hq1 C.hM hhalf

/-- The compact finite-product master order eventually controls the carrier,
the product response, every coordinate response, and trace simultaneously and
uniformly on the compact parameter sets. -/
theorem JointRemainderCompactSharpCertificateData.eventually_finProductMaster_norm_lt
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder directions n : ℕ}
    (C : JointRemainderCompactSharpCertificateData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder directions)
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ C.D.K, ∀ z ∈ C.D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          (C.finProductMasterOrder φ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (continuousLinearMapJointRemainderFinProductObservable φ)
          (C.finProductMasterOrder φ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon ∧
      (∀ i,
        ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
            (φ i) (C.finProductMasterOrder φ epsilon)
            taylorOrder tailOrder directions
            (C.D.H a) C.D.ds C.D.h
            (compressedJointRemainderBaseResolventFamily
              C.D.J C.D.Q taylorOrder (F a) lambda z)
            (compressedJointRemainderEndpointResolventFamily
              C.D.J C.D.Q taylorOrder directions (F a) lambda z
              (C.D.H a) C.D.ds C.D.h)‖ < epsilon) ∧
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V (C.finProductMasterOrder φ epsilon)
          taylorOrder tailOrder directions
          (C.D.H a) C.D.ds C.D.h
          (compressedJointRemainderBaseResolventFamily
            C.D.J C.D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            C.D.J C.D.Q taylorOrder directions (F a) lambda z
            (C.D.H a) C.D.ds C.D.h)‖ < epsilon := by
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
  filter_upwards [hproduct, hcoords] with a hp hc
  intro lambda hlambda z hz
  have hp' := hp lambda hlambda z hz
  refine ⟨hp'.1,
    hp'.2.1 (continuousLinearMapJointRemainderFinProductObservable φ) (by simp),
    ?_, hp'.2.2⟩
  intro i
  exact hc (φ i)
    ((List.mem_ofFn' φ (φ i)).2 ⟨i, rfl⟩)
    lambda hlambda z hz

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
