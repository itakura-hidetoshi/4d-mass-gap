import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachTransfer
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
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

/-- Complete compact-uniform data for an exact joint Fréchet--Taylor
remainder tail.  Base and endpoint zero-free margins remain independent. -/
structure JointRemainderCompactData
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (taylorOrder m : ℕ) where
  S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F
  B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F
  L : ContinuousLinearMapOpenResolventNormBoundData E
  hLgap : L.gap = gap
  hLresolvent : L.resolvent = S.limitResolvent
  J : V →L[ℝ] E
  Q : E →L[ℝ] V
  H : α → Fin m → (V →L[ℝ] V)
  H0 : Fin m → (V →L[ℝ] V)
  hH : Tendsto H l (𝓝 H0)
  ds : ℝ
  h : Fin m → ℝ
  K : Set ℝ
  hKcompact : IsCompact K
  upper : ℝ
  hKupper : K ⊆ Set.Iic upper
  hupper : upper < gap
  Z : Set ℝ
  baseMargin : ℝ
  endMargin : ℝ
  hbaseMargin : 0 < baseMargin
  hendMargin : 0 < endMargin
  hlimitBaseMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    baseMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|
  hlimitEndMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    endMargin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z|
  Mbase : ℝ
  Mend : ℝ
  hMbase : 0 ≤ Mbase
  hMend : 0 ≤ Mend
  hlimitBaseNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ Mbase
  hlimitEndNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
    continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
        continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z ≤ Mend

/-- Base true-resolvent family over every ambient Taylor level. -/
def compressedJointRemainderBaseResolventFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder : ℕ)
    (G : ℝ → E →L[ℝ] E) (lambda z : ℝ) :
    Fin (taylorOrder + 1) → (V →L[ℝ] V) :=
  fun k => continuousLinearMapRealResolvent (V := V)
    (continuousLinearMapCompression J Q
      (_root_.iteratedDeriv k.1 G lambda)) z

/-- Endpoint true-resolvent family after the simultaneous increment. -/
def compressedJointRemainderEndpointResolventFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder m : ℕ)
    (G : ℝ → E →L[ℝ] E) (lambda z : ℝ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ) :
    Fin (taylorOrder + 1) → (V →L[ℝ] V) :=
  fun k => continuousLinearMapRealResolvent (V := V)
    (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 G lambda) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h) z

/-- Complete finite-dimensional compact input. -/
def compressedJointRemainderInput
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder m : ℕ)
    (G : ℝ → E →L[ℝ] E) (lambda z : ℝ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ) :
    ContinuousLinearMapJointTaylorDysonRemainderInput V taylorOrder m :=
  continuousLinearMapJointTaylorDysonRemainderInput
    (compressedJointRemainderBaseResolventFamily J Q taylorOrder G lambda z)
    (compressedJointRemainderEndpointResolventFamily
      J Q taylorOrder m G lambda z H ds h) H

/-- Compact-uniform base-family convergence. -/
theorem JointRemainderCompactData.baseFamily_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
      ‖compressedJointRemainderBaseResolventFamily
          D.J D.Q taylorOrder (F a) lambda z -
        compressedJointRemainderBaseResolventFamily
          D.J D.Q taylorOrder D.S.limitResolvent lambda z‖ < epsilon := by
  have hs :=
    D.S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product_jet
      D.B D.L D.hLgap D.hLresolvent D.J D.Q taylorOrder D.K D.hKcompact
      D.hKupper D.hupper D.Z D.baseMargin D.hbaseMargin
      (fun k hk lambda hlambda z hz =>
        D.hlimitBaseMargin ⟨k, Nat.lt_succ_iff.2 hk⟩ lambda hlambda z hz)
      D.Mbase D.hMbase
      (fun k hk lambda hlambda z hz =>
        D.hlimitBaseNorm ⟨k, Nat.lt_succ_iff.2 hk⟩ lambda hlambda z hz)
      epsilon hepsilon
  filter_upwards [hs] with a ha
  intro lambda hlambda z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  exact (ha k.1 (Nat.le_of_lt_succ k.isLt) lambda hlambda z hz).2.2

/-- Compact-uniform endpoint operator convergence before inversion. -/
theorem JointRemainderCompactData.endpointOperator_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ a in l, ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ D.K,
      ‖(continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 (F a) lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h) -
        (continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 D.S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h)‖ < eta := by
  have hhalf : 0 < eta / 2 := half_pos heta
  have hop :=
    D.S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression_jet
      D.B D.L D.hLgap D.hLresolvent D.J D.Q taylorOrder D.K D.hKcompact
      D.hKupper D.hupper (eta / 2) hhalf
  have hiT : Tendsto
      (fun a => continuousLinearMapJointSpectralOperatorRemainderIncrement
        m (D.H a) D.ds D.h) l
      (𝓝 (continuousLinearMapJointSpectralOperatorRemainderIncrement
        m D.H0 D.ds D.h)) :=
    ((continuous_continuousLinearMapJointSpectralOperatorRemainderIncrement
      (V := V) m D.ds D.h).tendsto D.H0).comp D.hH
  have hi : ∀ᶠ a in l,
      ‖continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h -
        continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h‖ < eta / 2 := by
    rw [Metric.tendsto_nhds] at hiT
    simpa [dist_eq_norm] using hiT (eta / 2) hhalf
  filter_upwards [hop, hi] with a ha hia
  intro k lambda hlambda
  calc
    ‖(continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 (F a) lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h) -
        (continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 D.S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h)‖ =
      ‖(continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 (F a) lambda) -
        continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 D.S.limitResolvent lambda)) +
        (continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h -
          continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h)‖ := by
      congr 1
      abel
    _ ≤ ‖continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 (F a) lambda) -
        continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 D.S.limitResolvent lambda)‖ +
        ‖continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h -
          continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h‖ :=
      norm_add_le _ _
    _ < eta / 2 + eta / 2 :=
      add_lt_add (ha k.1 (Nat.le_of_lt_succ k.isLt) lambda hlambda) hia
    _ = eta := by ring

/-- Compact-uniform endpoint-family convergence after inversion. -/
theorem JointRemainderCompactData.endpointFamily_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
      ‖compressedJointRemainderEndpointResolventFamily
          D.J D.Q taylorOrder m (F a) lambda z (D.H a) D.ds D.h -
        compressedJointRemainderEndpointResolventFamily
          D.J D.Q taylorOrder m D.S.limitResolvent lambda z D.H0 D.ds D.h‖ < epsilon := by
  let A := fun a : α => fun i : Fin (taylorOrder + 1) × ℝ =>
    continuousLinearMapCompression D.J D.Q
        (_root_.iteratedDeriv i.1.1 (F a) i.2) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h
  let A0 := fun i : Fin (taylorOrder + 1) × ℝ =>
    continuousLinearMapCompression D.J D.Q
        (_root_.iteratedDeriv i.1.1 D.S.limitResolvent i.2) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h
  let s : Set (Fin (taylorOrder + 1) × ℝ) := Set.univ ×ˢ D.K
  have hA : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖A a i - A0 i‖ < eta := by
    intro eta heta
    filter_upwards [JointRemainderCompactData.endpointOperator_tendsto D eta heta]
      with a ha
    intro i hi
    simpa [A, A0] using ha i.1 i.2 hi.2
  have hr := finiteDimensional_realResolvent_tendsto_uniformOn_set
    (V := V) A A0 hA D.Z D.endMargin D.hendMargin
    (fun i hi z hz => D.hlimitEndMargin i.1 i.2 hi.2 z hz)
    D.Mend D.hMend (fun i hi z hz => D.hlimitEndNorm i.1 i.2 hi.2 z hz)
    epsilon hepsilon
  filter_upwards [hr] with a ha
  intro lambda hlambda z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  have hk := ha (k, lambda) ⟨Set.mem_univ k, hlambda⟩ z hz
  simpa [A, A0, compressedJointRemainderEndpointResolventFamily] using hk

/-- Compact-uniform convergence of the complete nested input. -/
theorem JointRemainderCompactData.input_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ a in l, ∀ p ∈ D.K ×ˢ D.Z,
      ‖compressedJointRemainderInput D.J D.Q taylorOrder m
          (F a) p.1 p.2 (D.H a) D.ds D.h -
        compressedJointRemainderInput D.J D.Q taylorOrder m
          D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h‖ < eta := by
  exact
    (continuousLinearMapJointTaylorDysonRemainderInput_tendsto_uniform_of_components
      (s := D.K ×ˢ D.Z)
      (fun a p => compressedJointRemainderBaseResolventFamily
        D.J D.Q taylorOrder (F a) p.1 p.2)
      (fun p => compressedJointRemainderBaseResolventFamily
        D.J D.Q taylorOrder D.S.limitResolvent p.1 p.2)
      (fun a p => compressedJointRemainderEndpointResolventFamily
        D.J D.Q taylorOrder m (F a) p.1 p.2 (D.H a) D.ds D.h)
      (fun p => compressedJointRemainderEndpointResolventFamily
        D.J D.Q taylorOrder m D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h)
      D.H D.H0
      (fun e he => by
        filter_upwards [JointRemainderCompactData.baseFamily_tendsto D e he]
          with a ha
        exact fun p hp => ha p.1 hp.1 p.2 hp.2)
      (fun e he => by
        filter_upwards [JointRemainderCompactData.endpointFamily_tendsto D e he]
          with a ha
        exact fun p hp => ha p.1 hp.1 p.2 hp.2)
      D.hH) eta heta

/-- Uniform bound for the continuum complete input. -/
theorem JointRemainderCompactData.limitInput_norm_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (p : ℝ × ℝ) (hp : p ∈ D.K ×ˢ D.Z) :
    ‖compressedJointRemainderInput D.J D.Q taylorOrder m
        D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h‖ ≤
      max (max D.Mbase D.Mend) ‖D.H0‖ := by
  have hb : ‖compressedJointRemainderBaseResolventFamily
      D.J D.Q taylorOrder D.S.limitResolvent p.1 p.2‖ ≤ D.Mbase :=
    (pi_norm_le_iff_of_nonneg D.hMbase).2
      (fun k => D.hlimitBaseNorm k p.1 hp.1 p.2 hp.2)
  have he : ‖compressedJointRemainderEndpointResolventFamily
      D.J D.Q taylorOrder m D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h‖ ≤ D.Mend :=
    (pi_norm_le_iff_of_nonneg D.hMend).2
      (fun k => D.hlimitEndNorm k p.1 hp.1 p.2 hp.2)
  change max
    (max
      ‖compressedJointRemainderBaseResolventFamily
        D.J D.Q taylorOrder D.S.limitResolvent p.1 p.2‖
      ‖compressedJointRemainderEndpointResolventFamily
        D.J D.Q taylorOrder m D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h‖)
    ‖D.H0‖ ≤ max (max D.Mbase D.Mend) ‖D.H0‖
  exact max_le
    (max_le
      (hb.trans ((le_max_left D.Mbase D.Mend).trans (le_max_left _ _)))
      (he.trans ((le_max_right D.Mbase D.Mend).trans (le_max_left _ _))))
    (le_max_right _ _)

/-- Compact-uniform carrier remainder-tail convergence in the genuine norm. -/
theorem JointRemainderCompactData.carrier_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m (D.H a) D.ds D.h
          (compressedJointRemainderBaseResolventFamily D.J D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            D.J D.Q taylorOrder m (F a) lambda z (D.H a) D.ds D.h) -
        continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m D.H0 D.ds D.h
          (compressedJointRemainderBaseResolventFamily
            D.J D.Q taylorOrder D.S.limitResolvent lambda z)
          (compressedJointRemainderEndpointResolventFamily
            D.J D.Q taylorOrder m D.S.limitResolvent lambda z D.H0 D.ds D.h)‖ < epsilon := by
  let X := fun a : α => fun p : ℝ × ℝ =>
    compressedJointRemainderInput D.J D.Q taylorOrder m
      (F a) p.1 p.2 (D.H a) D.ds D.h
  let X0 := fun p : ℝ × ℝ =>
    compressedJointRemainderInput D.J D.Q taylorOrder m
      D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h
  let R : ℝ := max (max D.Mbase D.Mend) ‖D.H0‖
  have hR : 0 ≤ R := le_trans D.hMbase
    (le_trans (le_max_left D.Mbase D.Mend) (le_max_left _ _))
  have hX0 : ∀ p ∈ D.K ×ˢ D.Z, ‖X0 p‖ ≤ R := by
    intro p hp
    exact JointRemainderCompactData.limitInput_norm_le D p hp
  have ht :=
    finiteDimensional_jointTaylorDysonRemainderTailRectangularJet_tendsto_uniform
      (s := D.K ×ˢ D.Z) baseOrder taylorOrder tailOrder m D.ds D.h
      X X0 R hR hX0 (JointRemainderCompactData.input_tendsto D)
      epsilon hepsilon
  filter_upwards [ht] with a ha
  intro lambda hlambda z hz
  simpa [X, X0, compressedJointRemainderInput] using
    ha (lambda, z) ⟨hlambda, hz⟩

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compact-uniform arbitrary Banach-valued remainder-tail convergence. -/
theorem JointRemainderCompactData.response_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (baseOrder tailOrder : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m (D.H a) D.ds D.h
          (compressedJointRemainderBaseResolventFamily D.J D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            D.J D.Q taylorOrder m (F a) lambda z (D.H a) D.ds D.h) -
        continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m D.H0 D.ds D.h
          (compressedJointRemainderBaseResolventFamily
            D.J D.Q taylorOrder D.S.limitResolvent lambda z)
          (compressedJointRemainderEndpointResolventFamily
            D.J D.Q taylorOrder m D.S.limitResolvent lambda z D.H0 D.ds D.h)‖ < epsilon := by
  let X := fun a : α => fun p : ℝ × ℝ =>
    compressedJointRemainderInput D.J D.Q taylorOrder m
      (F a) p.1 p.2 (D.H a) D.ds D.h
  let X0 := fun p : ℝ × ℝ =>
    compressedJointRemainderInput D.J D.Q taylorOrder m
      D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h
  let R : ℝ := max (max D.Mbase D.Mend) ‖D.H0‖
  have hR : 0 ≤ R := le_trans D.hMbase
    (le_trans (le_max_left D.Mbase D.Mend) (le_max_left _ _))
  have hX0 : ∀ p ∈ D.K ×ˢ D.Z, ‖X0 p‖ ≤ R := by
    intro p hp
    exact JointRemainderCompactData.limitInput_norm_le D p hp
  have ht :=
    finiteDimensional_jointTaylorDysonRemainderTailResponseRectangularJet_tendsto_uniform
      (s := D.K ×ˢ D.Z) φ baseOrder taylorOrder tailOrder m D.ds D.h
      X X0 R hR hX0 (JointRemainderCompactData.input_tendsto D)
      epsilon hepsilon
  filter_upwards [ht] with a ha
  intro lambda hlambda z hz
  simpa [X, X0, compressedJointRemainderInput] using
    ha (lambda, z) ⟨hlambda, hz⟩

/-- Compact-uniform basis-independent trace remainder-tail convergence. -/
theorem JointRemainderCompactData.trace_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ}
    (D : JointRemainderCompactData (α := α) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) taylorOrder m)
    (baseOrder tailOrder : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m (D.H a) D.ds D.h
          (compressedJointRemainderBaseResolventFamily D.J D.Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            D.J D.Q taylorOrder m (F a) lambda z (D.H a) D.ds D.h) -
        continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m D.H0 D.ds D.h
          (compressedJointRemainderBaseResolventFamily
            D.J D.Q taylorOrder D.S.limitResolvent lambda z)
          (compressedJointRemainderEndpointResolventFamily
            D.J D.Q taylorOrder m D.S.limitResolvent lambda z D.H0 D.ds D.h)‖ < epsilon := by
  simpa [continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    JointRemainderCompactData.response_tendsto D
      (continuousLinearMapTrace (V := V)) baseOrder tailOrder epsilon hepsilon

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
