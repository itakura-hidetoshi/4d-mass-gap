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
    (compressedJointRemainderBaseResolventFamily
      J Q taylorOrder G lambda z)
    (compressedJointRemainderEndpointResolventFamily
      J Q taylorOrder m G lambda z H ds h)
    H

/-- Compact-uniform convergence of the complete base-resolvent family in its
finite-product norm. -/
theorem compressedJointRemainderBaseResolventFamily_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖compressedJointRemainderBaseResolventFamily
          J Q taylorOrder (F a) lambda z -
        compressedJointRemainderBaseResolventFamily
          J Q taylorOrder S.limitResolvent lambda z‖ < epsilon := by
  intro epsilon hepsilon
  have hstable :=
    S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product_jet
      B L hLgap hLresolvent J Q taylorOrder K hKcompact hKupper hupper Z
      margin hmargin
      (fun k hk lambda hlambda z hz =>
        hlimitMargin ⟨k, Nat.lt_succ_iff.2 hk⟩ lambda hlambda z hz)
      M hM
      (fun k hk lambda hlambda z hz =>
        hlimitNorm ⟨k, Nat.lt_succ_iff.2 hk⟩ lambda hlambda z hz)
      epsilon hepsilon
  filter_upwards [hstable] with a ha
  intro lambda hlambda z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  exact (ha k.1 (Nat.le_of_lt_succ k.isLt) lambda hlambda z hz).2.2

/-- Uniform convergence of all compressed endpoint operators, including the
moving direction family, before inversion. -/
theorem compressedJointRemainderEndpointOperatorFamily_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (ds : ℝ) (h : Fin m → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l,
      ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K,
      ‖(continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 (F a) lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m (H a) ds h) -
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h)‖ < eta := by
  intro eta heta
  have hhalf : 0 < eta / 2 := half_pos heta
  have hcompressed :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression_jet
      B L hLgap hLresolvent J Q taylorOrder K hKcompact hKupper hupper
      (eta / 2) hhalf
  have hincTendsto : Tendsto
      (fun a => continuousLinearMapJointSpectralOperatorRemainderIncrement
        m (H a) ds h) l
      (𝓝 (continuousLinearMapJointSpectralOperatorRemainderIncrement
        m H0 ds h)) :=
    (continuous_continuousLinearMapJointSpectralOperatorRemainderIncrement
      (V := V) m ds h).tendsto H0 |>.comp hH
  have hincrement : ∀ᶠ a in l,
      ‖continuousLinearMapJointSpectralOperatorRemainderIncrement m (H a) ds h -
        continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h‖ < eta / 2 := by
    rw [Metric.tendsto_nhds] at hincTendsto
    simpa [dist_eq_norm] using hincTendsto (eta / 2) hhalf
  filter_upwards [hcompressed, hincrement] with a ha hb
  intro k lambda hlambda
  calc
    ‖(continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 (F a) lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m (H a) ds h) -
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h)‖ =
      ‖(continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 (F a) lambda) -
        continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) +
        (continuousLinearMapJointSpectralOperatorRemainderIncrement m (H a) ds h -
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h)‖ := by
        congr 1
        abel
    _ ≤ ‖continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 (F a) lambda) -
        continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)‖ +
        ‖continuousLinearMapJointSpectralOperatorRemainderIncrement m (H a) ds h -
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h‖ :=
      norm_add_le _ _
    _ < eta / 2 + eta / 2 :=
      add_lt_add (ha k.1 (Nat.le_of_lt_succ k.isLt) lambda hlambda) hb
    _ = eta := by ring

/-- Compact-uniform convergence of the complete endpoint-resolvent family in
its finite-product norm. -/
theorem compressedJointRemainderEndpointResolventFamily_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (ds : ℝ) (h : Fin m → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖compressedJointRemainderEndpointResolventFamily
          J Q taylorOrder m (F a) lambda z (H a) ds h -
        compressedJointRemainderEndpointResolventFamily
          J Q taylorOrder m S.limitResolvent lambda z H0 ds h‖ < epsilon := by
  intro epsilon hepsilon
  let A := fun a : α => fun i : Fin (taylorOrder + 1) × ℝ =>
    continuousLinearMapCompression J Q
        (_root_.iteratedDeriv i.1.1 (F a) i.2) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement m (H a) ds h
  let A0 := fun i : Fin (taylorOrder + 1) × ℝ =>
    continuousLinearMapCompression J Q
        (_root_.iteratedDeriv i.1.1 S.limitResolvent i.2) +
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h
  let s : Set (Fin (taylorOrder + 1) × ℝ) := Set.univ ×ˢ K
  have hA : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖A a i - A0 i‖ < eta := by
    intro eta heta
    have h := S.compressedJointRemainderEndpointOperatorFamily_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q taylorOrder m H H0 hH ds h
      K hKcompact hKupper hupper eta heta
    filter_upwards [h] with a ha
    intro i hi
    exact ha i.1 i.2 hi.2
  have hres := finiteDimensional_realResolvent_tendsto_uniformOn_set
    A A0 hA Z margin hmargin
    (fun i hi z hz => hlimitMargin i.1 i.2 hi.2 z hz)
    M hM (fun i hi z hz => hlimitNorm i.1 i.2 hi.2 z hz)
    epsilon hepsilon
  filter_upwards [hres] with a ha
  intro lambda hlambda z hz
  apply (pi_norm_lt_iff hepsilon).2
  intro k
  exact ha (k, lambda) ⟨Set.mem_univ k, hlambda⟩ z hz

/-- The limit complete input is uniformly bounded by the maximum of the two
explicit continuum resolvent bounds and the direction-family norm. -/
theorem compressedJointRemainderInput_limit_norm_le
    {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData (Filter.principal Set.univ) gap F)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder m : ℕ)
    (H0 : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (lambda z : ℝ) (Mbase Mend : ℝ)
    (hMbase : 0 ≤ Mbase) (hMend : 0 ≤ Mend)
    (hbase : ∀ k : Fin (taylorOrder + 1),
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ Mbase)
    (hend : ∀ k : Fin (taylorOrder + 1),
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z ≤ Mend) :
    ‖compressedJointRemainderInput J Q taylorOrder m
        S.limitResolvent lambda z H0 ds h‖ ≤
      max (max Mbase Mend) ‖H0‖ := by
  rw [norm_prod_le_iff]
  constructor
  · rw [norm_prod_le_iff]
    constructor
    · apply le_trans
        ((pi_norm_le_iff_of_nonneg hMbase).2 (fun k => hbase k))
        (le_trans (le_max_left Mbase Mend) (le_max_left _ _))
    · apply le_trans
        ((pi_norm_le_iff_of_nonneg hMend).2 (fun k => hend k))
        (le_trans (le_max_right Mbase Mend) (le_max_left _ _))
  · exact le_max_right _ _

/-- Compact-uniform convergence of the complete carrier remainder-tail
rectangle in its genuine finite-product norm. -/
theorem jointRemainderTailRectangularJet_tendsto_uniformOn_compact_product_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (ds : ℝ) (h : Fin m → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (baseMargin endMargin : ℝ) (hbaseMargin : 0 < baseMargin)
    (hendMargin : 0 < endMargin)
    (hlimitBaseMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      baseMargin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (hlimitEndMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      endMargin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z|)
    (Mbase Mend : ℝ) (hMbase : 0 ≤ Mbase) (hMend : 0 ≤ Mend)
    (hlimitBaseNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ Mbase)
    (hlimitEndNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z ≤ Mend) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m (H a) ds h
          (compressedJointRemainderBaseResolventFamily J Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            J Q taylorOrder m (F a) lambda z (H a) ds h) -
        continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m H0 ds h
          (compressedJointRemainderBaseResolventFamily
            J Q taylorOrder S.limitResolvent lambda z)
          (compressedJointRemainderEndpointResolventFamily
            J Q taylorOrder m S.limitResolvent lambda z H0 ds h)‖ < epsilon := by
  intro epsilon hepsilon
  let X := fun a : α => fun p : ℝ × ℝ =>
    compressedJointRemainderInput J Q taylorOrder m
      (F a) p.1 p.2 (H a) ds h
  let X0 := fun p : ℝ × ℝ =>
    compressedJointRemainderInput J Q taylorOrder m
      S.limitResolvent p.1 p.2 H0 ds h
  let s : Set (ℝ × ℝ) := K ×ˢ Z
  have hb := S.compressedJointRemainderBaseResolventFamily_tendsto_uniformOn_compact_product
    B L hLgap hLresolvent J Q taylorOrder K hKcompact hKupper hupper Z
    baseMargin hbaseMargin hlimitBaseMargin Mbase hMbase hlimitBaseNorm
  have he := S.compressedJointRemainderEndpointResolventFamily_tendsto_uniformOn_compact_product
    B L hLgap hLresolvent J Q taylorOrder m H H0 hH ds h
    K hKcompact hKupper hupper Z endMargin hendMargin hlimitEndMargin
    Mend hMend hlimitEndNorm
  have hX := continuousLinearMapJointTaylorDysonRemainderInput_tendsto_uniform_of_components
    (fun a p => compressedJointRemainderBaseResolventFamily
      J Q taylorOrder (F a) p.1 p.2)
    (fun p => compressedJointRemainderBaseResolventFamily
      J Q taylorOrder S.limitResolvent p.1 p.2)
    (fun a p => compressedJointRemainderEndpointResolventFamily
      J Q taylorOrder m (F a) p.1 p.2 (H a) ds h)
    (fun p => compressedJointRemainderEndpointResolventFamily
      J Q taylorOrder m S.limitResolvent p.1 p.2 H0 ds h)
    H H0
    (fun eta heta => by
      filter_upwards [hb eta heta] with a ha
      exact fun p hp => ha p.1 hp.1 p.2 hp.2)
    (fun eta heta => by
      filter_upwards [he eta heta] with a ha
      exact fun p hp => ha p.1 hp.1 p.2 hp.2)
    hH
  let R : ℝ := max (max Mbase Mend) ‖H0‖
  have hR : 0 ≤ R := le_trans hMbase
    (le_trans (le_max_left Mbase Mend) (le_max_left _ _))
  have hX0 : ∀ p ∈ s, ‖X0 p‖ ≤ R := by
    intro p hp
    dsimp [X0, R]
    rw [norm_prod_le_iff]
    constructor
    · rw [norm_prod_le_iff]
      constructor
      · exact le_trans
          ((pi_norm_le_iff_of_nonneg hMbase).2
            (fun k => hlimitBaseNorm k p.1 hp.1 p.2 hp.2))
          (le_trans (le_max_left Mbase Mend) (le_max_left _ _))
      · exact le_trans
          ((pi_norm_le_iff_of_nonneg hMend).2
            (fun k => hlimitEndNorm k p.1 hp.1 p.2 hp.2))
          (le_trans (le_max_right Mbase Mend) (le_max_left _ _))
    · exact le_max_right _ _
  simpa [X, X0, s, compressedJointRemainderInput] using
    finiteDimensional_jointTaylorDysonRemainderTailRectangularJet_tendsto_uniform
      baseOrder taylorOrder tailOrder m ds h X X0 R hR hX0 hX
      epsilon hepsilon

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compact-uniform convergence of every Banach-valued observed exact
remainder-tail rectangle. -/
theorem jointRemainderTailResponseRectangularJet_tendsto_uniformOn_compact_product_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (ds : ℝ) (h : Fin m → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (baseMargin endMargin : ℝ) (hbaseMargin : 0 < baseMargin)
    (hendMargin : 0 < endMargin)
    (hlimitBaseMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      baseMargin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (hlimitEndMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      endMargin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z|)
    (Mbase Mend : ℝ) (hMbase : 0 ≤ Mbase) (hMend : 0 ≤ Mend)
    (hlimitBaseNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ Mbase)
    (hlimitEndNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z ≤ Mend) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m (H a) ds h
          (compressedJointRemainderBaseResolventFamily J Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            J Q taylorOrder m (F a) lambda z (H a) ds h) -
        continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m H0 ds h
          (compressedJointRemainderBaseResolventFamily
            J Q taylorOrder S.limitResolvent lambda z)
          (compressedJointRemainderEndpointResolventFamily
            J Q taylorOrder m S.limitResolvent lambda z H0 ds h)‖ < epsilon := by
  intro epsilon hepsilon
  have hcarrier := S.jointRemainderTailRectangularJet_tendsto_uniformOn_compact_product_norm
    B L hLgap hLresolvent J Q baseOrder taylorOrder tailOrder m H H0 hH ds h
    K hKcompact hKupper hupper Z baseMargin endMargin hbaseMargin hendMargin
    hlimitBaseMargin hlimitEndMargin Mbase Mend hMbase hMend
    hlimitBaseNorm hlimitEndNorm
    (epsilon / (‖φ‖ + 1)) (div_pos hepsilon (by positivity))
  filter_upwards [hcarrier] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_sub_norm_lt_iff
    _ _ hepsilon).2
  intro k j
  exact continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon
    ((continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_sub_norm_lt_iff
      _ _ (div_pos hepsilon (by positivity))).1
      (ha lambda hlambda z hz) k j)

/-- Compact-uniform convergence of the basis-independent trace exact
remainder-tail rectangle. -/
theorem jointRemainderTailTraceRectangularJet_tendsto_uniformOn_compact_product_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (ds : ℝ) (h : Fin m → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (baseMargin endMargin : ℝ) (hbaseMargin : 0 < baseMargin)
    (hendMargin : 0 < endMargin)
    (hlimitBaseMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      baseMargin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (hlimitEndMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      endMargin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z|)
    (Mbase Mend : ℝ) (hMbase : 0 ≤ Mbase) (hMend : 0 ≤ Mend)
    (hlimitBaseNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ Mbase)
    (hlimitEndNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k.1 S.limitResolvent lambda) +
          continuousLinearMapJointSpectralOperatorRemainderIncrement m H0 ds h) z ≤ Mend) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m (H a) ds h
          (compressedJointRemainderBaseResolventFamily J Q taylorOrder (F a) lambda z)
          (compressedJointRemainderEndpointResolventFamily
            J Q taylorOrder m (F a) lambda z (H a) ds h) -
        continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m H0 ds h
          (compressedJointRemainderBaseResolventFamily
            J Q taylorOrder S.limitResolvent lambda z)
          (compressedJointRemainderEndpointResolventFamily
            J Q taylorOrder m S.limitResolvent lambda z H0 ds h)‖ < epsilon := by
  simpa [continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    S.jointRemainderTailResponseRectangularJet_tendsto_uniformOn_compact_product_norm
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      baseOrder taylorOrder tailOrder m H H0 hH ds h K hKcompact
      hKupper hupper Z baseMargin endMargin hbaseMargin hendMargin
      hlimitBaseMargin hlimitEndMargin Mbase Mend hMbase hMend
      hlimitBaseNorm hlimitEndNorm

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
