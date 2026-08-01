import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterArbitraryDirectionFrechet
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationSymmetricMultilinearContinuity
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The ordered noncommutative Dyson carrier is continuous in the resolvent
operator for the operator norm on the full continuous multilinear-map space. -/
theorem continuous_continuousLinearMapRealResolventOrderedDysonMultilinearCarrier
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapRealResolventOrderedDysonMultilinear n R) := by
  let A := V →L[ℝ] V
  have houter : Continuous (fun R : A =>
      (ContinuousLinearMap.mul ℝ A).flip R) :=
    (ContinuousLinearMap.mul ℝ A).flip.continuous
  have hfamily : Continuous (fun R : A =>
      fun _ : Fin n => (ContinuousLinearMap.mul ℝ A) R) := by
    exact continuous_pi fun _ => (ContinuousLinearMap.mul ℝ A).continuous
  have hinner : Continuous (fun R : A =>
      (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A).compContinuousLinearMap
        (fun _ => (ContinuousLinearMap.mul ℝ A) R)) := by
    exact
      (ContinuousMultilinearMap.compContinuousLinearMapLRight
        (E := fun _ : Fin n => A)
        (ContinuousMultilinearMap.mkPiAlgebraFin ℝ n A)).cont.comp hfamily
  have hpost : Continuous (fun R : A =>
      ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin n => A) A A ((ContinuousLinearMap.mul ℝ A).flip R)) :=
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin n => A) A A).continuous.comp houter
  simpa [A, continuousLinearMapRealResolventOrderedDysonMultilinear] using
    hpost.eval hinner

/-- Every permuted ordered Dyson carrier is continuous in full multilinear-map
operator norm. -/
theorem continuous_continuousLinearMapRealResolventPermutedDysonMultilinearCarrier
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapRealResolventPermutedDysonMultilinear n R σ) := by
  simpa [continuousLinearMapRealResolventPermutedDysonMultilinear] using
    (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ (V →L[ℝ] V) (V →L[ℝ] V) σ).continuous.comp
      (continuous_continuousLinearMapRealResolventOrderedDysonMultilinearCarrier
        (V := V) n)

/-- The complete symmetric Dyson derivative carrier is continuous in the
resolvent operator for the operator norm on continuous multilinear maps. -/
theorem continuous_continuousLinearMapRealResolventSymmetricDysonMultilinearCarrier
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapRealResolventSymmetricDysonMultilinear n R) := by
  unfold continuousLinearMapRealResolventSymmetricDysonMultilinear
  apply continuous_finset_sum
  intro σ _hσ
  exact
    continuous_continuousLinearMapRealResolventPermutedDysonMultilinearCarrier
      (V := V) n σ

/-- Operator-norm convergence of resolvents transfers to operator-norm
convergence of the complete symmetric Dyson derivative carrier. -/
theorem tendsto_continuousLinearMapRealResolventSymmetricDysonMultilinearCarrier
    {V α : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter α} (n : ℕ) (R : α → (V →L[ℝ] V)) (R0 : V →L[ℝ] V)
    (hR : Tendsto R l (𝓝 R0)) :
    Tendsto (fun a =>
      continuousLinearMapRealResolventSymmetricDysonMultilinear n (R a)) l
      (𝓝 (continuousLinearMapRealResolventSymmetricDysonMultilinear n R0)) :=
  (continuous_continuousLinearMapRealResolventSymmetricDysonMultilinearCarrier
    n).continuousAt.tendsto.comp hR

/-- Pull the complete symmetric Dyson carrier back along the augmented joint
spectral/operator direction synthesis.  The input is the resolvent operator
itself, so this construction is continuous globally in operator norm. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin n => (Fin (m + 1) → ℝ)) (V →L[ℝ] V) :=
  (continuousLinearMapRealResolventSymmetricDysonMultilinear n R).compContinuousLinearMap
    (fun _ => continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H))

/-- The full joint multilinear carrier is continuous in the underlying
resolvent operator for its own operator norm. -/
theorem continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
        m n H R) := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent] using
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => continuousLinearMapFiniteParameterDirectionSynthesis (m + 1)
        (continuousLinearMapJointSpectralOperatorDirectionFamily m H))).continuous.comp
      (continuous_continuousLinearMapRealResolventSymmetricDysonMultilinearCarrier
        (V := V) n)

/-- At every joint base point, the existing genuine joint Fréchet derivative
carrier is exactly the globally continuous pullback carrier evaluated at the
corresponding shifted real resolvent. -/
theorem continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative_eq_multilinearCarrierFromResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (m n : ℕ) (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V))
    (z s : ℝ) (t : Fin m → ℝ) :
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative
        m n A H z s t =
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
        m n H (continuousLinearMapRealResolvent
          (continuousLinearMapFiniteParameterOperatorChart m A H t) (z + s)) := by
  rfl

/-- A finite jet of complete genuine joint Fréchet carriers, retaining the
operator norm of every continuous multilinear-map component. -/
def continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m N : ℕ) (H : Fin m → (V →L[ℝ] V)) (R : V →L[ℝ] V) :
    ∀ n : Fin N,
      ContinuousMultilinearMap ℝ
        (fun _ : Fin n.1 => (Fin (m + 1) → ℝ)) (V →L[ℝ] V) :=
  fun n =>
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
      m n.1 H R

end MathlibAnalytic
end MGAP4D
