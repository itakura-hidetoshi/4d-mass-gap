import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventHermiteCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α κ E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Simultaneous compact-uniform convergence for the full finite rectangle of
Taylor derivatives through `taylorOrder` and normalized Hermite coefficients
through `hermiteOrder`, uniformly over an arbitrary finite-node family. -/
theorem iteratedDeriv_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (taylorOrder hermiteOrder : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (nodes : κ → Fin (hermiteOrder + 1) → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ taylorOrder, ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k ≤ taylorOrder, ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ k ≤ taylorOrder, ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) (nodes q j)) -
          continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q j))‖ < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (taylorOrder + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) (nodes q j)) -
          continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q j))‖ < epsilon := by
    intro k hk
    have hkOrder : k ≤ taylorOrder :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact
      S.iteratedDeriv_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k hermiteOrder K hKcompact hKu hu
        nodes T Z hnodes margin hmargin (hlimitMargin k hkOrder)
        M hM (hlimitNorm k hkOrder) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (taylorOrder + 1),
      ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) (nodes q j)) -
          continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q j))‖ < epsilon := by
    change {a | ∀ k ∈ Finset.range (taylorOrder + 1),
      ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) (nodes q j)) -
          continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q j))‖ < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (taylorOrder + 1),
      ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) (nodes q j)) -
          continuousLinearMapRealResolventHermiteJet hermiteOrder
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q j))‖ < epsilon} =
      ⋂ k ∈ Finset.range (taylorOrder + 1), {a |
        ∀ lambda ∈ K, ∀ q ∈ T,
          ‖continuousLinearMapRealResolventHermiteJet hermiteOrder
              (fun j => continuousLinearMapRealResolvent
                (continuousLinearMapCompression J Q
                  (_root_.iteratedDeriv k (F a) lambda)) (nodes q j)) -
            continuousLinearMapRealResolventHermiteJet hermiteOrder
              (fun j => continuousLinearMapRealResolvent
                (continuousLinearMapCompression J Q
                  (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q j))‖ < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (taylorOrder + 1))).2
      fun k hk' => hk k hk'
  filter_upwards [hfinite] with a ha
  intro k hkOrder lambda hlambda q hq
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))
    lambda hlambda q hq

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
