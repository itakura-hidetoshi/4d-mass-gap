import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityClosedBox
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

/-- Complete data for arbitrary joint approximation-time/Taylor-degree nets on
a closed Taylor box, with a simultaneously moving finite direction family. -/
structure JointRemainderClosedBoxData
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} (directions : ℕ) where
  S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F
  B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F
  L : ContinuousLinearMapOpenResolventNormBoundData E
  hLgap : L.gap = gap
  hLresolvent : L.resolvent = S.limitResolvent
  J : V →L[ℝ] E
  Q : E →L[ℝ] V
  time : β → α
  degree : β → ℕ
  htime : Tendsto time n l
  hdegree : Tendsto degree n atTop
  H : β → Fin directions → (V →L[ℝ] V)
  H0 : Fin directions → (V →L[ℝ] V)
  hH : Tendsto H n (𝓝 H0)
  ds : ℝ
  h : Fin directions → ℝ
  box : ContinuousLinearMapClosedTaylorParameterBox gap
  Z : Set ℝ
  baseMargin : ℝ
  endMargin : ℝ
  hbaseMargin : 0 < baseMargin
  hendMargin : 0 < endMargin
  hlimitBaseMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
    baseMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|
  hlimitEndMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
    endMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions H0 ds h) z|
  Mbase : ℝ
  Mend : ℝ
  hMbase : 0 ≤ Mbase
  hMend : 0 ≤ Mend
  hlimitBaseNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ Mbase
  hlimitEndNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions H0 ds h) z ≤ Mend

private abbrev ExplicitJointRemainderClosedBoxData
    (l : Filter α) (gap : ℝ) (F : α → ℝ → E →L[ℝ] E)
    (n : Filter β) (directions : ℕ) :=
  JointRemainderClosedBoxData (α := α) (β := β) (E := E) (V := V)
    (l := l) (gap := gap) (F := F) (n := n) directions

private abbrev ClosedBoxRemainderIndex :=
  ContinuousLinearMapTaylorParameterPoint × ℝ

/-- The one-level true base-resolvent family of an approximating Taylor
partial sum. -/
def closedBoxJointRemainderApproxBaseFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (G : ℝ → E →L[ℝ] E) (degree : ℕ)
    (p : ContinuousLinearMapTaylorParameterPoint) (z : ℝ) :
    Fin 1 → (V →L[ℝ] V) :=
  fun _ => continuousLinearMapRealResolvent (V := V)
    (continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum G p.center p.target degree)) z

/-- The one-level continuum base-resolvent family. -/
def closedBoxJointRemainderLimitBaseFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (G0 : ℝ → E →L[ℝ] E)
    (p : ContinuousLinearMapTaylorParameterPoint) (z : ℝ) :
    Fin 1 → (V →L[ℝ] V) :=
  fun _ => continuousLinearMapRealResolvent (V := V)
    (continuousLinearMapCompression J Q (G0 p.target)) z

/-- The one-level endpoint-resolvent family of an approximating Taylor partial
sum after the simultaneous spectral/operator increment. -/
def closedBoxJointRemainderApproxEndpointFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (directions : ℕ)
    (G : ℝ → E →L[ℝ] E) (degree : ℕ)
    (p : ContinuousLinearMapTaylorParameterPoint) (z : ℝ)
    (H : Fin directions → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin directions → ℝ) : Fin 1 → (V →L[ℝ] V) :=
  fun _ => continuousLinearMapRealResolvent (V := V)
    (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum G p.center p.target degree) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions H ds h) z

/-- The one-level continuum endpoint-resolvent family. -/
def closedBoxJointRemainderLimitEndpointFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (directions : ℕ)
    (G0 : ℝ → E →L[ℝ] E)
    (p : ContinuousLinearMapTaylorParameterPoint) (z : ℝ)
    (H0 : Fin directions → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin directions → ℝ) : Fin 1 → (V →L[ℝ] V) :=
  fun _ => continuousLinearMapRealResolvent (V := V)
    (continuousLinearMapCompression J Q (G0 p.target) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions H0 ds h) z

/-- Complete one-level closed-box remainder input. -/
def closedBoxJointRemainderApproxInput
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (directions : ℕ)
    (G : ℝ → E →L[ℝ] E) (degree : ℕ)
    (p : ContinuousLinearMapTaylorParameterPoint) (z : ℝ)
    (H : Fin directions → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin directions → ℝ) :
    ContinuousLinearMapJointTaylorDysonRemainderInput V 0 directions :=
  continuousLinearMapJointTaylorDysonRemainderInput
    (closedBoxJointRemainderApproxBaseFamily J Q G degree p z)
    (closedBoxJointRemainderApproxEndpointFamily
      J Q directions G degree p z H ds h) H

/-- Complete one-level continuum closed-box remainder input. -/
def closedBoxJointRemainderLimitInput
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (directions : ℕ)
    (G0 : ℝ → E →L[ℝ] E)
    (p : ContinuousLinearMapTaylorParameterPoint) (z : ℝ)
    (H0 : Fin directions → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin directions → ℝ) :
    ContinuousLinearMapJointTaylorDysonRemainderInput V 0 directions :=
  continuousLinearMapJointTaylorDysonRemainderInput
    (closedBoxJointRemainderLimitBaseFamily J Q G0 p z)
    (closedBoxJointRemainderLimitEndpointFamily
      J Q directions G0 p z H0 ds h) H0

/-- Closed-box convergence of the one-level base true-resolvent family. -/
theorem JointRemainderClosedBoxData.baseFamily_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, D.box.Contains p → ∀ z ∈ D.Z,
      ‖closedBoxJointRemainderApproxBaseFamily D.J D.Q
          (F (D.time b)) (D.degree b) p z -
        closedBoxJointRemainderLimitBaseFamily
          D.J D.Q D.S.limitResolvent p z‖ < epsilon := by
  have hres :=
    D.S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      D.B D.L D.hLgap D.hLresolvent D.J D.Q D.time D.degree
      D.htime D.hdegree D.box D.Z D.baseMargin D.hbaseMargin
      D.hlimitBaseMargin D.Mbase D.hMbase D.hlimitBaseNorm epsilon hepsilon
  filter_upwards [hres] with b hb
  intro p hp z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  simpa [closedBoxJointRemainderApproxBaseFamily,
    closedBoxJointRemainderLimitBaseFamily] using hb p hp z hz

/-- Closed-box convergence of endpoint operators before inversion. -/
theorem JointRemainderClosedBoxData.endpointOperator_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ b in n, ∀ p, D.box.Contains p →
      ‖(continuousLinearMapCompression D.J D.Q
          (continuousLinearMapTaylorPartialSum
            (F (D.time b)) p.center p.target (D.degree b)) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement
            directions (D.H b) D.ds D.h) -
        (continuousLinearMapCompression D.J D.Q
          (D.S.limitResolvent p.target) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement
            directions D.H0 D.ds D.h)‖ < eta := by
  have hhalf : 0 < eta / 2 := half_pos heta
  have hop :=
    D.S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
      D.B D.L D.hLgap D.hLresolvent D.J D.Q D.time D.degree
      D.htime D.hdegree D.box.delta_le_gap D.box.lambda_bounds
      D.box.lambdaMax_lt_delta D.box.rMax_nonneg D.box.rMax_lt_margin
      (eta / 2) hhalf
  have hincTendsto : Tendsto
      (fun b => continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions (D.H b) D.ds D.h) n
      (𝓝 (continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions D.H0 D.ds D.h)) :=
    ((continuous_continuousLinearMapJointSpectralOperatorRemainderIncrement
      (V := V) directions D.ds D.h).tendsto D.H0).comp D.hH
  have hinc : ∀ᶠ b in n,
      ‖continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions (D.H b) D.ds D.h -
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions D.H0 D.ds D.h‖ < eta / 2 := by
    rw [Metric.tendsto_nhds] at hincTendsto
    simpa [dist_eq_norm] using hincTendsto (eta / 2) hhalf
  filter_upwards [hop, hinc] with b hb hbi
  intro p hp
  have hbp := hb p.center p.radius p.target
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  calc
    ‖(continuousLinearMapCompression D.J D.Q
          (continuousLinearMapTaylorPartialSum
            (F (D.time b)) p.center p.target (D.degree b)) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement
            directions (D.H b) D.ds D.h) -
        (continuousLinearMapCompression D.J D.Q
          (D.S.limitResolvent p.target) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement
            directions D.H0 D.ds D.h)‖ =
      ‖(continuousLinearMapCompression D.J D.Q
          (continuousLinearMapTaylorPartialSum
            (F (D.time b)) p.center p.target (D.degree b)) -
        continuousLinearMapCompression D.J D.Q
          (D.S.limitResolvent p.target)) +
        (continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions (D.H b) D.ds D.h -
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions D.H0 D.ds D.h)‖ := by
      congr 1
      abel
    _ ≤ ‖continuousLinearMapCompression D.J D.Q
          (continuousLinearMapTaylorPartialSum
            (F (D.time b)) p.center p.target (D.degree b)) -
        continuousLinearMapCompression D.J D.Q
          (D.S.limitResolvent p.target)‖ +
        ‖continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions (D.H b) D.ds D.h -
        continuousLinearMapJointSpectralOperatorRemainderIncrement
          directions D.H0 D.ds D.h‖ := norm_add_le _ _
    _ < eta / 2 + eta / 2 := add_lt_add hbp hbi
    _ = eta := by ring

/-- Closed-box convergence of the one-level endpoint true-resolvent family. -/
theorem JointRemainderClosedBoxData.endpointFamily_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, D.box.Contains p → ∀ z ∈ D.Z,
      ‖closedBoxJointRemainderApproxEndpointFamily D.J D.Q directions
          (F (D.time b)) (D.degree b) p z (D.H b) D.ds D.h -
        closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
          D.S.limitResolvent p z D.H0 D.ds D.h‖ < epsilon := by
  let A := fun b : β => fun p : ContinuousLinearMapTaylorParameterPoint =>
    continuousLinearMapCompression D.J D.Q
        (continuousLinearMapTaylorPartialSum
          (F (D.time b)) p.center p.target (D.degree b)) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions (D.H b) D.ds D.h
  let A0 := fun p : ContinuousLinearMapTaylorParameterPoint =>
    continuousLinearMapCompression D.J D.Q (D.S.limitResolvent p.target) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement
        directions D.H0 D.ds D.h
  have hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in n, ∀ p ∈ {p | D.box.Contains p}, ‖A b p - A0 p‖ < eta := by
    intro eta heta
    filter_upwards [JointRemainderClosedBoxData.endpointOperator_tendsto D eta heta]
      with b hb
    intro p hp
    simpa [A, A0] using hb p hp
  have hres := finiteDimensional_realResolvent_tendsto_uniformOn_set
    (V := V) A A0 hA D.Z D.endMargin D.hendMargin
    D.hlimitEndMargin D.Mend D.hMend D.hlimitEndNorm epsilon hepsilon
  filter_upwards [hres] with b hb
  intro p hp z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  have hk := hb p hp z hz
  simpa [A, A0, closedBoxJointRemainderApproxEndpointFamily,
    closedBoxJointRemainderLimitEndpointFamily] using hk

/-- Closed-box convergence of the complete nested remainder input. -/
theorem JointRemainderClosedBoxData.input_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ b in n, ∀ q ∈ {q : ClosedBoxRemainderIndex |
      D.box.Contains q.1 ∧ q.2 ∈ D.Z},
      ‖closedBoxJointRemainderApproxInput D.J D.Q directions
          (F (D.time b)) (D.degree b) q.1 q.2 (D.H b) D.ds D.h -
        closedBoxJointRemainderLimitInput D.J D.Q directions
          D.S.limitResolvent q.1 q.2 D.H0 D.ds D.h‖ < eta := by
  exact
    (continuousLinearMapJointTaylorDysonRemainderInput_tendsto_uniform_of_components
      (s := {q : ClosedBoxRemainderIndex |
        D.box.Contains q.1 ∧ q.2 ∈ D.Z})
      (fun b q => closedBoxJointRemainderApproxBaseFamily
        D.J D.Q (F (D.time b)) (D.degree b) q.1 q.2)
      (fun q => closedBoxJointRemainderLimitBaseFamily
        D.J D.Q D.S.limitResolvent q.1 q.2)
      (fun b q => closedBoxJointRemainderApproxEndpointFamily
        D.J D.Q directions (F (D.time b)) (D.degree b)
          q.1 q.2 (D.H b) D.ds D.h)
      (fun q => closedBoxJointRemainderLimitEndpointFamily
        D.J D.Q directions D.S.limitResolvent q.1 q.2 D.H0 D.ds D.h)
      D.H D.H0
      (fun e hepos => by
        filter_upwards [JointRemainderClosedBoxData.baseFamily_tendsto D e hepos]
          with b hb
        exact fun q hq => hb q.1 hq.1 q.2 hq.2)
      (fun e hepos => by
        filter_upwards [JointRemainderClosedBoxData.endpointFamily_tendsto D e hepos]
          with b hb
        exact fun q hq => hb q.1 hq.1 q.2 hq.2)
      D.hH) eta heta

/-- The continuum one-level input is uniformly bounded. -/
theorem JointRemainderClosedBoxData.limitInput_norm_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (q : ClosedBoxRemainderIndex)
    (hq : D.box.Contains q.1 ∧ q.2 ∈ D.Z) :
    ‖closedBoxJointRemainderLimitInput D.J D.Q directions
        D.S.limitResolvent q.1 q.2 D.H0 D.ds D.h‖ ≤
      max (max D.Mbase D.Mend) ‖D.H0‖ := by
  have hb :
      ‖closedBoxJointRemainderLimitBaseFamily
        D.J D.Q D.S.limitResolvent q.1 q.2‖ ≤ D.Mbase :=
    (pi_norm_le_iff_of_nonneg D.hMbase).2
      (fun _ => D.hlimitBaseNorm q.1 hq.1 q.2 hq.2)
  have he :
      ‖closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
        D.S.limitResolvent q.1 q.2 D.H0 D.ds D.h‖ ≤ D.Mend :=
    (pi_norm_le_iff_of_nonneg D.hMend).2
      (fun _ => D.hlimitEndNorm q.1 hq.1 q.2 hq.2)
  change max
    (max
      ‖closedBoxJointRemainderLimitBaseFamily
        D.J D.Q D.S.limitResolvent q.1 q.2‖
      ‖closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
        D.S.limitResolvent q.1 q.2 D.H0 D.ds D.h‖)
    ‖D.H0‖ ≤ max (max D.Mbase D.Mend) ‖D.H0‖
  exact max_le
    (max_le
      (hb.trans ((le_max_left D.Mbase D.Mend).trans (le_max_left _ _)))
      (he.trans ((le_max_right D.Mbase D.Mend).trans (le_max_left _ _))))
    (le_max_right _ _)

/-- Arbitrary joint-net closed-box convergence of the exact carrier remainder
tail in the genuine finite-product norm. -/
theorem JointRemainderClosedBoxData.carrier_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, D.box.Contains p → ∀ z ∈ D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder 0 tailOrder directions (D.H b) D.ds D.h
          (closedBoxJointRemainderApproxBaseFamily
            D.J D.Q (F (D.time b)) (D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily D.J D.Q directions
            (F (D.time b)) (D.degree b) p z (D.H b) D.ds D.h) -
        continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder 0 tailOrder directions D.H0 D.ds D.h
          (closedBoxJointRemainderLimitBaseFamily
            D.J D.Q D.S.limitResolvent p z)
          (closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
            D.S.limitResolvent p z D.H0 D.ds D.h)‖ < epsilon := by
  let X := fun b : β => fun q : ClosedBoxRemainderIndex =>
    closedBoxJointRemainderApproxInput D.J D.Q directions
      (F (D.time b)) (D.degree b) q.1 q.2 (D.H b) D.ds D.h
  let X0 := fun q : ClosedBoxRemainderIndex =>
    closedBoxJointRemainderLimitInput D.J D.Q directions
      D.S.limitResolvent q.1 q.2 D.H0 D.ds D.h
  let s := {q : ClosedBoxRemainderIndex |
    D.box.Contains q.1 ∧ q.2 ∈ D.Z}
  let R : ℝ := max (max D.Mbase D.Mend) ‖D.H0‖
  have hR : 0 ≤ R := le_trans D.hMbase
    (le_trans (le_max_left D.Mbase D.Mend) (le_max_left _ _))
  have hX0 : ∀ q ∈ s, ‖X0 q‖ ≤ R := by
    intro q hq
    exact JointRemainderClosedBoxData.limitInput_norm_le D q hq
  have htransfer :=
    finiteDimensional_jointTaylorDysonRemainderTailRectangularJet_tendsto_uniform
      (s := s) baseOrder 0 tailOrder directions D.ds D.h X X0 R hR hX0
      (JointRemainderClosedBoxData.input_tendsto D) epsilon hepsilon
  filter_upwards [htransfer] with b hb
  intro p hp z hz
  simpa [X, X0, s, closedBoxJointRemainderApproxInput,
    closedBoxJointRemainderLimitInput] using hb (p, z) ⟨hp, hz⟩

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Arbitrary joint-net closed-box convergence of every Banach-valued observed
exact remainder tail. -/
theorem JointRemainderClosedBoxData.response_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (baseOrder tailOrder : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, D.box.Contains p → ∀ z ∈ D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder 0 tailOrder directions (D.H b) D.ds D.h
          (closedBoxJointRemainderApproxBaseFamily
            D.J D.Q (F (D.time b)) (D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily D.J D.Q directions
            (F (D.time b)) (D.degree b) p z (D.H b) D.ds D.h) -
        continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder 0 tailOrder directions D.H0 D.ds D.h
          (closedBoxJointRemainderLimitBaseFamily
            D.J D.Q D.S.limitResolvent p z)
          (closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
            D.S.limitResolvent p z D.H0 D.ds D.h)‖ < epsilon := by
  let X := fun b : β => fun q : ClosedBoxRemainderIndex =>
    closedBoxJointRemainderApproxInput D.J D.Q directions
      (F (D.time b)) (D.degree b) q.1 q.2 (D.H b) D.ds D.h
  let X0 := fun q : ClosedBoxRemainderIndex =>
    closedBoxJointRemainderLimitInput D.J D.Q directions
      D.S.limitResolvent q.1 q.2 D.H0 D.ds D.h
  let s := {q : ClosedBoxRemainderIndex |
    D.box.Contains q.1 ∧ q.2 ∈ D.Z}
  let R : ℝ := max (max D.Mbase D.Mend) ‖D.H0‖
  have hR : 0 ≤ R := le_trans D.hMbase
    (le_trans (le_max_left D.Mbase D.Mend) (le_max_left _ _))
  have hX0 : ∀ q ∈ s, ‖X0 q‖ ≤ R := by
    intro q hq
    exact JointRemainderClosedBoxData.limitInput_norm_le D q hq
  have htransfer :=
    finiteDimensional_jointTaylorDysonRemainderTailResponseRectangularJet_tendsto_uniform
      (s := s) φ baseOrder 0 tailOrder directions D.ds D.h X X0 R hR hX0
      (JointRemainderClosedBoxData.input_tendsto D) epsilon hepsilon
  filter_upwards [htransfer] with b hb
  intro p hp z hz
  simpa [X, X0, s, closedBoxJointRemainderApproxInput,
    closedBoxJointRemainderLimitInput] using hb (p, z) ⟨hp, hz⟩

/-- Arbitrary joint-net closed-box convergence of the basis-independent trace
exact remainder tail. -/
theorem JointRemainderClosedBoxData.trace_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : ExplicitJointRemainderClosedBoxData l gap F n directions)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ b in n, ∀ p, D.box.Contains p → ∀ z ∈ D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder 0 tailOrder directions (D.H b) D.ds D.h
          (closedBoxJointRemainderApproxBaseFamily
            D.J D.Q (F (D.time b)) (D.degree b) p z)
          (closedBoxJointRemainderApproxEndpointFamily D.J D.Q directions
            (F (D.time b)) (D.degree b) p z (D.H b) D.ds D.h) -
        continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder 0 tailOrder directions D.H0 D.ds D.h
          (closedBoxJointRemainderLimitBaseFamily
            D.J D.Q D.S.limitResolvent p z)
          (closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
            D.S.limitResolvent p z D.H0 D.ds D.h)‖ < epsilon := by
  simpa [continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    JointRemainderClosedBoxData.response_tendsto D
      (continuousLinearMapTrace (V := V)) baseOrder tailOrder epsilon hepsilon

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D