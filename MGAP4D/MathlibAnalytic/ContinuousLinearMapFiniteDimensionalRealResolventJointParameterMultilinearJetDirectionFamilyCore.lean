import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetSupCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- Direction synthesis bundled as a continuous linear map in the entire finite
operator-direction family. -/
noncomputable def continuousLinearMapFiniteParameterDirectionSynthesisFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) :
    (Fin m → (V →L[ℝ] V)) →L[ℝ]
      ((Fin m → ℝ) →L[ℝ] (V →L[ℝ] V)) :=
  ∑ j : Fin m,
    ((ContinuousLinearMap.smulRightL ℝ (Fin m → ℝ) (V →L[ℝ] V))
      (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)).comp
        (ContinuousLinearMap.proj j :
          (Fin m → (V →L[ℝ] V)) →L[ℝ] (V →L[ℝ] V))

@[simp]
theorem continuousLinearMapFiniteParameterDirectionSynthesisFamily_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : ℕ) (H : Fin m → (V →L[ℝ] V)) :
    continuousLinearMapFiniteParameterDirectionSynthesisFamily m H =
      continuousLinearMapFiniteParameterDirectionSynthesis m H := by
  ext t
  simp [continuousLinearMapFiniteParameterDirectionSynthesisFamily,
    continuousLinearMapFiniteParameterDirectionSynthesis_apply]

/-- The augmented spectral/operator direction family varies continuously in
all of its operator directions at once. -/
theorem continuous_continuousLinearMapJointSpectralOperatorDirectionFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) :
    Continuous (fun H : Fin m → (V →L[ℝ] V) =>
      continuousLinearMapJointSpectralOperatorDirectionFamily m H) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ ?_ j
  · exact continuous_const
  · intro k
    exact continuous_apply k

/-- The augmented parameter-direction synthesis is continuous in the complete
finite operator-direction family. -/
theorem continuous_continuousLinearMapJointSpectralOperatorDirectionSynthesis
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) :
    Continuous (fun H : Fin m → (V →L[ℝ] V) =>
      continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)) := by
  have hfun :
      (fun H : Fin m → (V →L[ℝ] V) =>
        continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
          (continuousLinearMapJointSpectralOperatorDirectionFamily m H)) =
      (continuousLinearMapFiniteParameterDirectionSynthesisFamily
        (V := V) (m + 1)) ∘
        (fun H : Fin m → (V →L[ℝ] V) =>
          continuousLinearMapJointSpectralOperatorDirectionFamily m H) := by
    funext H
    symm
    exact
      continuousLinearMapFiniteParameterDirectionSynthesisFamily_apply
        (V := V) (m + 1)
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
  rw [hfun]
  exact
    (continuousLinearMapFiniteParameterDirectionSynthesisFamily
      (V := V) (m + 1)).continuous.comp
        (continuous_continuousLinearMapJointSpectralOperatorDirectionFamily
          (V := V) m)

/-- The complete joint spectral/operator Fréchet carrier is jointly continuous
when both the compressed resolvent and the entire finite perturbation family
vary in operator norm. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent_directionFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m n : ℕ) :
    Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
        m n p.2 p.1) := by
  let compose :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin n => (Fin (m + 1) → ℝ))
        (fun _ : Fin n => (V →L[ℝ] V)) (V →L[ℝ] V)
  have hinner : Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      fun _ : Fin n =>
        continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
          (continuousLinearMapJointSpectralOperatorDirectionFamily m p.2)) := by
    apply continuous_pi
    intro _i
    exact
      (continuous_continuousLinearMapJointSpectralOperatorDirectionSynthesis
        (V := V) m).comp continuous_snd
  have hcompose : Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      compose (fun _ : Fin n =>
        continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
          (continuousLinearMapJointSpectralOperatorDirectionFamily m p.2))) :=
    compose.coe_continuous.comp hinner
  have houter : Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapRealResolventSymmetricDysonMultilinear n p.1) :=
    (continuous_continuousLinearMapRealResolventSymmetricDysonMultilinearCarrier
      (V := V) n).comp continuous_fst
  simpa [compose,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent] using
    hcompose.clm_apply houter

/-- Every finite complete joint Fréchet carrier jet is jointly continuous in
the resolvent and in the complete finite perturbation family. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent_directionFamily
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m N : ℕ) :
    Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
        m N p.2 p.1) := by
  apply continuous_pi
  intro n
  exact
    continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent_directionFamily
      (V := V) m n.1

/-- Banach-valued observations of complete joint Fréchet carriers remain
jointly continuous under simultaneous resolvent and direction-family motion. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent_directionFamily
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ) :
    Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n p.2 p.1) := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent] using
    (continuousLinearMapPostcomposeContinuousMultilinearMap n φ).continuous.comp
      (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent_directionFamily
        (V := V) m n)

/-- The complete finite Banach-valued response jet is jointly continuous in
both moving inputs. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent_directionFamily
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m order : ℕ) :
    Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
        φ m order p.2 p.1) := by
  apply continuous_pi
  intro n
  exact
    continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent_directionFamily
      φ m n.1

/-- The basis-independent complete trace jet is jointly continuous in the
compressed resolvent and in every finite perturbation direction. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent_directionFamily
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (m order : ℕ) :
    Continuous (fun p :
      (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
        V m order p.2 p.1) := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent] using
    continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent_directionFamily
      (continuousLinearMapTrace (V := V)) m order

end MathlibAnalytic
end MGAP4D
