import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetOperatorNormCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Postcomposition by a continuous linear observation, bundled as a continuous
linear map between complete continuous multilinear-map carrier spaces. -/
noncomputable def continuousLinearMapPostcomposeContinuousMultilinearMap
    {E G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (φ : G →L[ℝ] W) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) W :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin n => E) G W) φ

@[simp]
theorem continuousLinearMapPostcomposeContinuousMultilinearMap_apply
    {E G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (φ : G →L[ℝ] W)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G) :
    continuousLinearMapPostcomposeContinuousMultilinearMap n φ f =
      φ.compContinuousMultilinearMap f :=
  rfl

/-- Operator-norm control for postcomposition of a complete multilinear
carrier. -/
theorem continuousLinearMapPostcomposeContinuousMultilinearMap_norm_le
    {E G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (φ : G →L[ℝ] W)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G) :
    ‖continuousLinearMapPostcomposeContinuousMultilinearMap n φ f‖ ≤
      ‖φ‖ * ‖f‖ := by
  simpa [continuousLinearMapPostcomposeContinuousMultilinearMap] using
    φ.norm_compContinuousMultilinearMap_le f

/-- A complete Banach-valued observation of the joint spectral/operator
Fréchet carrier, before choosing any individual direction tuple. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (Fin (m + 1) → ℝ)) W :=
  φ.compContinuousMultilinearMap
    (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
      m n H R)

/-- The complete observed carrier remains globally continuous in the compressed
resolvent operator. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n H R) := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent] using
    (continuousLinearMapPostcomposeContinuousMultilinearMap n φ).continuous.comp
      (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
        m n H)

/-- Postcomposition controls the operator-norm difference of two complete
joint Fréchet carriers. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent_sub_norm_le
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (R S : V →L[ℝ] V) :
    ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n H R -
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n H S‖ ≤
      ‖φ‖ *
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
            m n H R -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
            m n H S‖ := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent,
    map_sub] using
    φ.norm_compContinuousMultilinearMap_le
      (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m n H R -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m n H S)

/-- The basis-independent trace of the complete joint Fréchet carrier. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (Fin (m + 1) → ℝ)) ℝ :=
  continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
    (continuousLinearMapTrace (V := V)) m n H R

/-- The full trace carrier is globally continuous in compressed resolvent
operator norm. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
        V m n H R) :=
  continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
    (continuousLinearMapTrace (V := V)) m n H

/-- A finite jet of complete basis-independent trace carriers. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierJetFromResolvent
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m N : ℕ) (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ
        (fun _ : Fin n.1 => (Fin (m + 1) → ℝ)) ℝ :=
  fun n =>
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
      V m n.1 H R

end MathlibAnalytic
end MGAP4D
