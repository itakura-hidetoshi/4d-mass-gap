import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventLinearResponseTransfer
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJetFiniteDimensionalCompressionTraceDeterminantLimit
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The basis-independent trace response of a finite-dimensional real
resolvent. -/
def continuousLinearMapRealResolventTraceResponse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  continuousLinearMapTrace (continuousLinearMapRealResolvent A z)

/-- Multipoint Hermite coefficient of the trace response. -/
def continuousLinearMapRealResolventHermiteTraceCoefficient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (order : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (order + 1) → ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapRealResolventHermiteCoefficient order A nodes)

/-- Finite Hermite jet of trace responses. -/
def continuousLinearMapRealResolventHermiteTraceJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (order : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (order + 1) → ℝ) : Fin (order + 1) → ℝ :=
  fun n => continuousLinearMapTrace
    (continuousLinearMapRealResolventHermiteJet order
      (fun j => continuousLinearMapRealResolvent A (nodes j)) n)

/-- Newton-Hermite interpolant of the trace response. -/
def continuousLinearMapRealResolventNewtonHermiteTraceInterpolant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapRealResolventNewtonHermiteInterpolant degree A nodes z)

/-- Exact Newton-Hermite remainder of the trace response. -/
def continuousLinearMapRealResolventNewtonHermiteTraceRemainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ) : ℝ :=
  continuousLinearMapTrace
    (continuousLinearMapRealResolventNewtonHermiteRemainder degree A nodes z)

/-- Apply the trace simultaneously to an interpolant/exact-remainder pair. -/
def continuousLinearMapRealResolventTracePair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (P : Fin 2 → (V →L[ℝ] V)) : Fin 2 → ℝ :=
  fun i => continuousLinearMapTrace (P i)

/-- Trace pairs depend continuously on the operator pair in product supremum
norm. -/
theorem continuous_continuousLinearMapRealResolventTracePair
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    Continuous
      (continuousLinearMapRealResolventTracePair
        (V := V)) := by
  unfold continuousLinearMapRealResolventTracePair
  apply continuous_pi
  intro i
  exact continuousLinearMapTrace.continuous.comp (continuous_apply i)

/-- Full-diagonal Hermite trace coefficients are factorially scaled true
spectral derivatives of the trace response. -/
theorem factorial_mul_continuousLinearMapRealResolventHermiteTraceCoefficient_const_eq_iteratedDeriv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (U : Set ℝ) (M : ℝ)
    (hU : IsOpen U) (hM : 0 ≤ M)
    (hunit : ∀ z ∈ U, IsUnit (continuousLinearMapRealShift A z))
    (hnorm : ∀ z ∈ U, continuousLinearMapRealResolventNorm A z ≤ M)
    (order : ℕ) {z : ℝ} (hz : z ∈ U) :
    (order.factorial : ℝ) *
        continuousLinearMapRealResolventHermiteTraceCoefficient
          order A (fun _ => z) =
      continuousLinearMapTrace
        (iteratedDeriv order (continuousLinearMapRealResolvent A) z) := by
  exact factorial_mul_continuousLinearMapRealResolventHermiteResponseCoefficient_const_eq_iteratedDeriv
    continuousLinearMapTrace A U M hU hM hunit hnorm order hz

/-- Exact Newton-Hermite interpolation formula for the trace response. -/
theorem continuousLinearMapRealResolventTraceResponse_eq_newtonHermiteTraceInterpolant_add_remainder
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z : ℝ)
    (hnodes : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (hz : IsUnit (continuousLinearMapRealShift A z)) :
    continuousLinearMapRealResolventTraceResponse A z =
      continuousLinearMapRealResolventNewtonHermiteTraceInterpolant
          degree A nodes z +
        continuousLinearMapRealResolventNewtonHermiteTraceRemainder
          degree A nodes z := by
  exact continuousLinearMapRealResolventLinearResponse_eq_newtonHermiteResponseInterpolant_add_remainder
    degree continuousLinearMapTrace A nodes z hnodes hz

/-- Trace interpolation is exact at every listed node, including repeated
nodes. -/
theorem continuousLinearMapRealResolventNewtonHermiteTraceInterpolant_eq_at_node
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ)
    (hnodes : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (i : Fin (degree + 1)) :
    continuousLinearMapRealResolventNewtonHermiteTraceInterpolant
        degree A nodes (nodes i) =
      continuousLinearMapRealResolventTraceResponse A (nodes i) := by
  exact continuousLinearMapRealResolventNewtonHermiteResponseInterpolant_eq_at_node
    degree continuousLinearMapTrace A nodes hnodes i

/-- Explicit trace interpolation-error estimate inherited from the exact
operator remainder. -/
theorem abs_continuousLinearMapRealResolventTraceResponse_sub_newtonHermiteTraceInterpolant_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (degree : ℕ) (A : V →L[ℝ] V)
    (nodes : Fin (degree + 1) → ℝ) (z M D : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hnodesUnit : ∀ i, IsUnit (continuousLinearMapRealShift A (nodes i)))
    (hzUnit : IsUnit (continuousLinearMapRealShift A z))
    (hnodesDist : ∀ i, |z - nodes i| ≤ D)
    (hnodesNorm : ∀ i, ‖continuousLinearMapRealResolvent A (nodes i)‖ ≤ M)
    (hzNorm : ‖continuousLinearMapRealResolvent A z‖ ≤ M) :
    |continuousLinearMapRealResolventTraceResponse A z -
        continuousLinearMapRealResolventNewtonHermiteTraceInterpolant
          degree A nodes z| ≤
      ‖(continuousLinearMapTrace : (V →L[ℝ] V) →L[ℝ] ℝ)‖ *
        (D ^ (degree + 1) * M ^ (degree + 2)) := by
  exact abs_continuousLinearMapRealResolventLinearResponse_sub_newtonHermiteResponseInterpolant_le
    degree continuousLinearMapTrace A nodes z M D hM hD
    hnodesUnit hzUnit hnodesDist hnodesNorm hzNorm

/-- Uniform convergence of operator pairs transfers to simultaneous trace
convergence of both pair components. -/
theorem finiteDimensional_tracePair_tendsto_uniformOn
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (P : α → ι → Fin 2 → (V →L[ℝ] V))
    (P0 : ι → Fin 2 → (V →L[ℝ] V))
    (hP : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ q ∈ s, ‖P a q - P0 q‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ q ∈ s,
        ‖continuousLinearMapRealResolventTracePair (P a q) -
          continuousLinearMapRealResolventTracePair (P0 q)‖ < epsilon := by
  intro epsilon hepsilon
  let c : ℝ :=
    ‖(continuousLinearMapTrace : (V →L[ℝ] V) →L[ℝ] ℝ)‖
  let eta : ℝ := epsilon / (c + 1)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact norm_nonneg _
  have hc1 : 0 < c + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hc1
  have hpair := hP eta heta
  filter_upwards [hpair] with a ha
  intro q hq
  rw [pi_norm_lt_iff hepsilon]
  intro i
  have hi : ‖P a q i - P0 q i‖ < eta := by
    have hp := ha q hq
    rw [pi_norm_lt_iff heta] at hp
    simpa only [Pi.sub_apply] using hp i
  have htrace := continuousLinearMapTrace_sub_abs_le (P a q i) (P0 q i)
  calc
    ‖(continuousLinearMapRealResolventTracePair (P a q) -
        continuousLinearMapRealResolventTracePair (P0 q)) i‖ =
        |continuousLinearMapTrace (P a q i) -
          continuousLinearMapTrace (P0 q i)| := by
            simp [continuousLinearMapRealResolventTracePair, Real.norm_eq_abs]
    _ ≤ c * ‖P a q i - P0 q i‖ := by simpa [c] using htrace
    _ ≤ (c + 1) * ‖P a q i - P0 q i‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (c + 1) * eta := mul_lt_mul_of_pos_left hi hc1
    _ = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hc1]

end MathlibAnalytic
end MGAP4D
