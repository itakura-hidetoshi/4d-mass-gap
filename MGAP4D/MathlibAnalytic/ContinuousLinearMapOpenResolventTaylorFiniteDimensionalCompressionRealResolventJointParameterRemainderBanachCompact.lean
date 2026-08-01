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

/-- All analytic data needed for compact-uniform stability of a complete exact
joint Fréchet--Taylor remainder tail.  The two positive determinant margins
and two continuum inverse bounds are explicit and independent. -/
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

/-- The base true-resolvent family for every compressed ambient Taylor level. -/
def compressedJointRemainderBaseResolventFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder : ℕ)
    (G : ℝ → E →L[ℝ] E) (lambda z : ℝ) :
    Fin (taylorOrder + 1) → (V →L[ℝ] V) :=
  fun k => continuousLinearMapRealResolvent
    (continuousLinearMapCompression J Q
      (_root_.iteratedDeriv k.1 G lambda)) z

/-- The endpoint true-resolvent family after the complete simultaneous
spectral/operator increment. -/
def compressedJointRemainderEndpointResolventFamily
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder m : ℕ)
    (G : ℝ → E →L[ℝ] E) (lambda z : ℝ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ) :
    Fin (taylorOrder + 1) → (V →L[ℝ] V) :=
  fun k => continuousLinearMapRealResolvent
    (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 G lambda) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h) z

/-- The complete finite-dimensional input supplying both resolvent families
and the moving direction family. -/
def compressedJointRemainderInput
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder m : ℕ)
    (G : ℝ → E →L[ℝ] E) (lambda z : ℝ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ) :
    ContinuousLinearMapJointTaylorDysonRemainderInput V taylorOrder m :=
  continuousLinearMapJointTaylorDysonRemainderInput
    (compressedJointRemainderBaseResolventFamily J Q taylorOrder G lambda z)
    (compressedJointRemainderEndpointResolventFamily
      J Q taylorOrder m G lambda z H ds h) H

/-- Compact-uniform convergence of the complete base true-resolvent family. -/
theorem JointRemainderCompactData.baseResolventFamily_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ a in l, ∀ lambda ∈ D.K, ∀ z ∈ D.Z,
      ‖compressedJointRemainderBaseResolventFamily
          D.J D.Q taylorOrder (F a) lambda z -
        compressedJointRemainderBaseResolventFamily
          D.J D.Q taylorOrder D.S.limitResolvent lambda z‖ < epsilon := by
  have hstable :=
    D.S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product_jet
      D.B D.L D.hLgap D.hLresolvent D.J D.Q taylorOrder D.K D.hKcompact
      D.hKupper D.hupper D.Z D.baseMargin D.hbaseMargin
      (fun k hk lambda hlambda z hz =>
        D.hlimitBaseMargin ⟨k, Nat.lt_succ_iff.2 hk⟩ lambda hlambda z hz)
      D.Mbase D.hMbase
      (fun k hk lambda hlambda z hz =>
        D.hlimitBaseNorm ⟨k, Nat.lt_succ_iff.2 hk⟩ lambda hlambda z hz)
      epsilon hepsilon
  filter_upwards [hstable] with a ha
  intro lambda hlambda z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  exact (ha k.1 (Nat.le_of_lt_succ k.isLt) lambda hlambda z hz).2.2

/-- Uniform convergence of all compressed endpoint operators, including the
moving direction family, before inversion. -/
theorem JointRemainderCompactData.endpointOperatorFamily_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ a in l, ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ D.K,
      ‖(continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 (F a) lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h) -
        (continuousLinearMapCompression D.J D.Q
          (_root_.iteratedDeriv k.1 D.S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h)‖ < eta := by
  have hhalf : 0 < eta / 2 := half_pos heta
  have hcompressed :=
    D.S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression_jet
      D.B D.L D.hLgap D.hLresolvent D.J D.Q taylorOrder D.K D.hKcompact
      D.hKupper D.hupper (eta / 2) hhalf
  have hincTendsto : Tendsto
      (fun a => continuousLinearMapJointSpectralOperatorRemainderIncrement
        m (D.H a) D.ds D.h) l
      (𝓝 (continuousLinearMapJointSpectralOperatorRemainderIncrement
        m D.H0 D.ds D.h)) :=
    (continuous_continuousLinearMapJointSpectralOperatorRemainderIncrement
      (V := V) m D.ds D.h).tendsto D.H0 |>.comp D.hH
  have hincrement : ∀ᶠ a in l,
      ‖continuousLinearMapJointSpectralOperatorRemainderIncrement m (D.H a) D.ds D.h -
        continuousLinearMapJointSpectralOperatorRemainderIncrement m D.H0 D.ds D.h‖ < eta / 2 := by
    rw [Metric.tendsto_nhds] at hincTendsto
    simpa [dist_eq_norm] using hincTendsto (eta / 2) hhalf
  filter_upwards [hcompressed, hincrement] with a ha hb
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
      add_lt_add (ha k.1 (Nat.le_of_lt_succ k.isLt) lambda hlambda) hb
    _ = eta := by ring

/-- Compact-uniform convergence of the complete endpoint true-resolvent family. -/
theorem JointRemainderCompactData.endpointResolventFamily_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
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
    filter_upwards [D.endpointOperatorFamily_tendsto eta heta] with a ha
    intro i hi
    exact ha i.1 i.2 hi.2
  have hres := finiteDimensional_realResolvent_tendsto_uniformOn_set
    A A0 hA D.Z D.endMargin D.hendMargin
    (fun i hi z hz => D.hlimitEndMargin i.1 i.2 hi.2 z hz)
    D.Mend D.hMend (fun i hi z hz => D.hlimitEndNorm i.1 i.2 hi.2 z hz)
    epsilon hepsilon
  filter_upwards [hres] with a ha
  intro lambda hlambda z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  exact ha (k, lambda) ⟨Set.mem_univ k, hlambda⟩ z hz

/-- Compact-uniform convergence of the complete nested input in its actual
finite-dimensional norm. -/
theorem JointRemainderCompactData.input_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ a in l, ∀ p ∈ D.K ×ˢ D.Z,
      ‖compressedJointRemainderInput D.J D.Q taylorOrder m
          (F a) p.1 p.2 (D.H a) D.ds D.h -
        compressedJointRemainderInput D.J D.Q taylorOrder m
          D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h‖ < eta := by
  have hb := D.baseResolventFamily_tendsto
  have he := D.endpointResolventFamily_tendsto
  exact continuousLinearMapJointTaylorDysonRemainderInput_tendsto_uniform_of_components
    (fun a p => compressedJointRemainderBaseResolventFamily
      D.J D.Q taylorOrder (F a) p.1 p.2)
    (fun p => compressedJointRemainderBaseResolventFamily
      D.J D.Q taylorOrder D.S.limitResolvent p.1 p.2)
    (fun a p => compressedJointRemainderEndpointResolventFamily
      D.J D.Q taylorOrder m (F a) p.1 p.2 (D.H a) D.ds D.h)
    (fun p => compressedJointRemainderEndpointResolventFamily
      D.J D.Q taylorOrder m D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h)
    D.H D.H0
    (fun e hepos => by
      filter_upwards [hb e hepos] with a ha
      exact fun p hp => ha p.1 hp.1 p.2 hp.2)
    (fun e hepos => by
      filter_upwards [he e hepos] with a ha
      exact fun p hp => ha p.1 hp.1 p.2 hp.2)
    D.hH eta heta

/-- The continuum complete input is bounded by the explicit common radius. -/
theorem JointRemainderCompactData.limitInput_norm_le
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
    (p : ℝ × ℝ) (hp : p ∈ D.K ×ˢ D.Z) :
    ‖compressedJointRemainderInput D.J D.Q taylorOrder m
        D.S.limitResolvent p.1 p.2 D.H0 D.ds D.h‖ ≤
      max (max D.Mbase D.Mend) ‖D.H0‖ := by
  rw [norm_prod_le_iff]
  constructor
  · rw [norm_prod_le_iff]
    constructor
    · exact le_trans
        ((pi_norm_le_iff_of_nonneg D.hMbase).2
          (fun k => D.hlimitBaseNorm k p.1 hp.1 p.2 hp.2))
        (le_trans (le_max_left D.Mbase D.Mend) (le_max_left _ _))
    · exact le_trans
        ((pi_norm_le_iff_of_nonneg D.hMend).2
          (fun k => D.hlimitEndNorm k p.1 hp.1 p.2 hp.2))
        (le_trans (le_max_right D.Mbase D.Mend) (le_max_left _ _))
  · exact le_max_right _ _

/-- Compact-uniform convergence of the complete carrier exact-remainder tail
in the genuine finite-product norm. -/
theorem JointRemainderCompactData.carrier_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
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
    exact D.limitInput_norm_le p hp
  simpa [X, X0, compressedJointRemainderInput] using
    finiteDimensional_jointTaylorDysonRemainderTailRectangularJet_tendsto_uniform
      baseOrder taylorOrder tailOrder m D.ds D.h X X0 R hR hX0
      D.input_tendsto epsilon hepsilon

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compact-uniform convergence of every Banach-valued observation of the
complete exact-remainder tail. -/
theorem JointRemainderCompactData.response_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
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
    exact D.limitInput_norm_le p hp
  simpa [X, X0, compressedJointRemainderInput] using
    finiteDimensional_jointTaylorDysonRemainderTailResponseRectangularJet_tendsto_uniform
      φ baseOrder taylorOrder tailOrder m D.ds D.h X X0 R hR hX0
      D.input_tendsto epsilon hepsilon

/-- Compact-uniform convergence of the basis-independent trace of the
complete exact-remainder tail. -/
theorem JointRemainderCompactData.trace_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {taylorOrder m : ℕ} (D : JointRemainderCompactData taylorOrder m)
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
    D.response_tendsto (continuousLinearMapTrace (V := V))
      baseOrder tailOrder epsilon hepsilon

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
