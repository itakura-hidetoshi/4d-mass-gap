import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorLocallyUniformJointLimit
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- A quantitative noncommutative power-difference estimate.  Only the common
operator-norm bound is used; no commutativity assumption is introduced. -/
theorem continuousLinearMap_pow_succ_sub_pow_succ_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : E →L[ℝ] E) {q : ℝ} (hq : 0 ≤ q)
    (hA : ‖A‖ ≤ q) (hB : ‖B‖ ≤ q) (n : ℕ) :
    ‖A ^ (n + 1) - B ^ (n + 1)‖ ≤
      ((n : ℝ) + 1) * q ^ n * ‖A - B‖ := by
  have hpowA : ∀ m : ℕ, ‖A ^ m‖ ≤ q ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
        calc
          ‖A ^ Nat.succ m‖ = ‖A ^ m * A‖ := by rw [pow_succ]
          _ ≤ ‖A ^ m‖ * ‖A‖ := norm_mul_le _ _
          _ ≤ q ^ m * q :=
            mul_le_mul hm hA (norm_nonneg A) (pow_nonneg hq m)
          _ = q ^ Nat.succ m := by rw [pow_succ]
  induction n with
  | zero => simpa using (le_refl ‖A - B‖)
  | succ n ih =>
      have hdecomp :
          A ^ (n + 2) - B ^ (n + 2) =
            A ^ (n + 1) * (A - B) +
              (A ^ (n + 1) - B ^ (n + 1)) * B := by
        noncomm_ring
      rw [show Nat.succ n + 1 = n + 2 by omega, hdecomp]
      calc
        ‖A ^ (n + 1) * (A - B) +
            (A ^ (n + 1) - B ^ (n + 1)) * B‖ ≤
          ‖A ^ (n + 1) * (A - B)‖ +
            ‖(A ^ (n + 1) - B ^ (n + 1)) * B‖ :=
          norm_add_le _ _
        _ ≤
            ‖A ^ (n + 1)‖ * ‖A - B‖ +
              ‖A ^ (n + 1) - B ^ (n + 1)‖ * ‖B‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤
            q ^ (n + 1) * ‖A - B‖ +
              (((n : ℝ) + 1) * q ^ n * ‖A - B‖) * q := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              (hpowA (n + 1)) (norm_nonneg (A - B))
          · exact mul_le_mul ih hB (norm_nonneg B) (by positivity)
        _ = ((Nat.succ n : ℝ) + 1) * q ^ Nat.succ n * ‖A - B‖ := by
          rw [Nat.cast_succ, pow_succ]
          ring

namespace ContinuousLinearMapOpenResolventNormBoundData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]

/-- The reciprocal distance from a closed subgap half-line bounds every
resolvent value on that half-line. -/
theorem resolvent_norm_le_on_Iic
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {u lambda : ℝ} (hu : u < D.gap) (hlambda : lambda ≤ u) :
    ‖D.resolvent lambda‖ ≤ (D.gap - u)⁻¹ := by
  have hlambdaGap : lambda < D.gap := lt_of_le_of_lt hlambda hu
  have hmargin : 0 < D.gap - u := sub_pos.mpr hu
  have hinv : (D.gap - lambda)⁻¹ ≤ (D.gap - u)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hmargin
        (by linarith : D.gap - u ≤ D.gap - lambda)
  exact le_trans (D.resolvent_norm_le hlambdaGap) hinv

/-- Every fixed Taylor-jet level is operator-norm Lipschitz on a closed subgap
half-line.  This is a direct resolvent-identity estimate, not an operator-norm
limit assertion. -/
theorem iteratedDeriv_sub_norm_le_on_Iic
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    (k : ℕ) {u lambda mu : ℝ} (hu : u < D.gap)
    (hlambda : lambda ≤ u) (hmu : mu ≤ u) :
    ‖_root_.iteratedDeriv k D.resolvent lambda -
        _root_.iteratedDeriv k D.resolvent mu‖ ≤
      |lambda - mu| *
        ((k.factorial : ℝ) *
          (((k : ℝ) + 1) * (D.gap - u)⁻¹ ^ k *
            ((D.gap - u)⁻¹ * (D.gap - u)⁻¹))) := by
  let q : ℝ := (D.gap - u)⁻¹
  have hmargin : 0 < D.gap - u := sub_pos.mpr hu
  have hq0 : 0 ≤ q := inv_nonneg.mpr hmargin.le
  have hlambdaGap : lambda < D.gap := lt_of_le_of_lt hlambda hu
  have hmuGap : mu < D.gap := lt_of_le_of_lt hmu hu
  have hA : ‖D.resolvent lambda‖ ≤ q := by
    simpa [q] using D.resolvent_norm_le_on_Iic hu hlambda
  have hB : ‖D.resolvent mu‖ ≤ q := by
    simpa [q] using D.resolvent_norm_le_on_Iic hu hmu
  have hpower :=
    continuousLinearMap_pow_succ_sub_pow_succ_norm_le
      (D.resolvent lambda) (D.resolvent mu) hq0 hA hB k
  have hsub := D.resolvent_sub_norm_le_on_Iic hu hlambda hmu
  have hcoef0 : 0 ≤ ((k : ℝ) + 1) * q ^ k := by positivity
  rw [(D.toContinuousLinearMapOpenResolventData).iteratedDeriv
        k hlambdaGap,
      (D.toContinuousLinearMapOpenResolventData).iteratedDeriv
        k hmuGap]
  calc
    ‖(k.factorial : ℝ) • (D.resolvent lambda) ^ (k + 1) -
        (k.factorial : ℝ) • (D.resolvent mu) ^ (k + 1)‖ =
      (k.factorial : ℝ) *
        ‖(D.resolvent lambda) ^ (k + 1) -
          (D.resolvent mu) ^ (k + 1)‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (k.factorial : ℝ) *
        (((k : ℝ) + 1) * q ^ k *
          ‖D.resolvent lambda - D.resolvent mu‖) :=
      mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _)
    _ ≤ (k.factorial : ℝ) *
        (((k : ℝ) + 1) * q ^ k *
          (|lambda - mu| * (q * q))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsub hcoef0)
        (Nat.cast_nonneg _)
    _ = |lambda - mu| *
        ((k.factorial : ℝ) *
          (((k : ℝ) + 1) * (D.gap - u)⁻¹ ^ k *
            ((D.gap - u)⁻¹ * (D.gap - u)⁻¹))) := by
      dsimp [q]
      ring

/-- Vector-valued equicontinuity of every fixed Taylor-jet level. -/
theorem iteratedDeriv_sub_apply_norm_le_on_Iic
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    (k : ℕ) {u lambda mu : ℝ} (hu : u < D.gap)
    (hlambda : lambda ≤ u) (hmu : mu ≤ u) (x : E) :
    ‖(_root_.iteratedDeriv k D.resolvent lambda) x -
        (_root_.iteratedDeriv k D.resolvent mu) x‖ ≤
      |lambda - mu| *
        (((k.factorial : ℝ) *
          (((k : ℝ) + 1) * (D.gap - u)⁻¹ ^ k *
            ((D.gap - u)⁻¹ * (D.gap - u)⁻¹))) * ‖x‖) := by
  calc
    ‖(_root_.iteratedDeriv k D.resolvent lambda) x -
        (_root_.iteratedDeriv k D.resolvent mu) x‖ =
      ‖(_root_.iteratedDeriv k D.resolvent lambda -
          _root_.iteratedDeriv k D.resolvent mu) x‖ := by simp
    _ ≤ ‖_root_.iteratedDeriv k D.resolvent lambda -
          _root_.iteratedDeriv k D.resolvent mu‖ * ‖x‖ :=
      (_root_.iteratedDeriv k D.resolvent lambda -
        _root_.iteratedDeriv k D.resolvent mu).le_opNorm x
    _ ≤
        (|lambda - mu| *
          ((k.factorial : ℝ) *
            (((k : ℝ) + 1) * (D.gap - u)⁻¹ ^ k *
              ((D.gap - u)⁻¹ * (D.gap - u)⁻¹)))) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (D.iteratedDeriv_sub_norm_le_on_Iic k hu hlambda hmu)
        (norm_nonneg x)
    _ = |lambda - mu| *
        (((k.factorial : ℝ) *
          (((k : ℝ) + 1) * (D.gap - u)⁻¹ ^ k *
            ((D.gap - u)⁻¹ * (D.gap - u)⁻¹))) * ‖x‖) := by
      ring

end ContinuousLinearMapOpenResolventNormBoundData

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Pointwise strong convergence of one fixed Taylor-jet level upgrades to
uniform strong convergence on every compact subgap spectral set. -/
theorem iteratedDeriv_tendsto_uniformOn_compact_apply
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (x : E) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖(_root_.iteratedDeriv k (F a) lambda) x -
          (_root_.iteratedDeriv k S.limitResolvent lambda) x‖ < epsilon := by
  intro epsilon hepsilon
  let q : ℝ := (gap - u)⁻¹
  let c : ℝ :=
    ((k.factorial : ℝ) *
      (((k : ℝ) + 1) * q ^ k * (q * q))) * ‖x‖
  have hmargin : 0 < gap - u := sub_pos.mpr hu
  have hq0 : 0 ≤ q := inv_nonneg.mpr hmargin.le
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  let eta : ℝ := epsilon / (3 * (c + 1))
  have hc1 : 0 < c + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon (mul_pos (by norm_num) hc1)
  have hetaC : eta * c < epsilon / 3 := by
    have hcLt : c < c + 1 := lt_add_one c
    have hmul := mul_lt_mul_of_pos_left hcLt heta
    calc
      eta * c < eta * (c + 1) := by simpa [mul_comm] using hmul
      _ = epsilon / 3 := by
        dsimp [eta]
        field_simp [ne_of_gt hc1]
  let U : K → Set ℝ := fun y => Metric.ball y.1 eta
  have hUopen : ∀ y : K, IsOpen (U y) := fun y => Metric.isOpen_ball
  have hcover : K ⊆ ⋃ y : K, U y := by
    intro lambda hlambda
    apply mem_iUnion.2
    exact ⟨⟨lambda, hlambda⟩, Metric.mem_ball_self heta⟩
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover U hUopen hcover
  have hcenter : ∀ y : K,
      ∀ᶠ a in l,
        ‖(_root_.iteratedDeriv k (F a) y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent y.1) x‖ < epsilon / 3 := by
    intro y
    have hyGap : y.1 < gap := lt_of_le_of_lt (hKu y.2) hu
    have hy := S.iteratedDeriv_tendsto_apply k (lambda := y.1) hyGap x
    rw [Metric.tendsto_nhds] at hy
    have hyEventually := hy (epsilon / 3) (div_pos hepsilon (by norm_num))
    simpa [dist_eq_norm] using hyEventually
  have hfinite : ∀ᶠ a in l, ∀ y ∈ t,
      ‖(_root_.iteratedDeriv k (F a) y.1) x -
        (_root_.iteratedDeriv k S.limitResolvent y.1) x‖ < epsilon / 3 := by
    change {a | ∀ y ∈ t,
      ‖(_root_.iteratedDeriv k (F a) y.1) x -
        (_root_.iteratedDeriv k S.limitResolvent y.1) x‖ < epsilon / 3} ∈ l
    rw [show {a | ∀ y ∈ t,
        ‖(_root_.iteratedDeriv k (F a) y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent y.1) x‖ < epsilon / 3} =
      ⋂ y ∈ t,
        {a | ‖(_root_.iteratedDeriv k (F a) y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent y.1) x‖ < epsilon / 3} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem t).2 fun y hy => hcenter y
  filter_upwards [hfinite] with a ha
  intro lambda hlambdaK
  have hlambdaCover := ht hlambdaK
  rcases mem_iUnion.1 hlambdaCover with ⟨y, hyCover⟩
  rcases mem_iUnion.1 hyCover with ⟨hyt, hlambdaBall⟩
  have hlambdaU : lambda ≤ u := hKu hlambdaK
  have hyU : y.1 ≤ u := hKu y.2
  have hdist : |lambda - y.1| < eta := by
    simpa [U, Real.dist_eq] using hlambdaBall
  have hFamilyGap : u < (B.normBoundData a).gap := by
    rw [B.gap_eq a]
    exact hu
  have hFamilyBound0 :=
    (B.normBoundData a).iteratedDeriv_sub_apply_norm_le_on_Iic
      k hFamilyGap hlambdaU hyU x
  have hFamilyBound :
      ‖(_root_.iteratedDeriv k (F a) lambda) x -
        (_root_.iteratedDeriv k (F a) y.1) x‖ ≤
        |lambda - y.1| * c := by
    rw [B.gap_eq a, B.resolvent_eq a] at hFamilyBound0
    simpa [c, q] using hFamilyBound0
  have hFamilySmall :
      ‖(_root_.iteratedDeriv k (F a) lambda) x -
        (_root_.iteratedDeriv k (F a) y.1) x‖ < epsilon / 3 := by
    refine lt_of_le_of_lt hFamilyBound ?_
    calc
      |lambda - y.1| * c ≤ eta * c :=
        mul_le_mul_of_nonneg_right (le_of_lt hdist) hc0
      _ < epsilon / 3 := hetaC
  have hLimitGap : u < L.gap := by rw [hLgap]; exact hu
  have hLimitBound0 :=
    L.iteratedDeriv_sub_apply_norm_le_on_Iic k hLimitGap hyU hlambdaU x
  have hLimitBound :
      ‖(_root_.iteratedDeriv k S.limitResolvent y.1) x -
        (_root_.iteratedDeriv k S.limitResolvent lambda) x‖ ≤
        |y.1 - lambda| * c := by
    rw [hLgap, hLresolvent] at hLimitBound0
    simpa [c, q] using hLimitBound0
  have hLimitSmall :
      ‖(_root_.iteratedDeriv k S.limitResolvent y.1) x -
        (_root_.iteratedDeriv k S.limitResolvent lambda) x‖ < epsilon / 3 := by
    refine lt_of_le_of_lt hLimitBound ?_
    calc
      |y.1 - lambda| * c = |lambda - y.1| * c := by rw [abs_sub_comm]
      _ ≤ eta * c := mul_le_mul_of_nonneg_right (le_of_lt hdist) hc0
      _ < epsilon / 3 := hetaC
  have hdecomp :
      (_root_.iteratedDeriv k (F a) lambda) x -
          (_root_.iteratedDeriv k S.limitResolvent lambda) x =
        ((_root_.iteratedDeriv k (F a) lambda) x -
          (_root_.iteratedDeriv k (F a) y.1) x) +
        ((_root_.iteratedDeriv k (F a) y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent y.1) x) +
        ((_root_.iteratedDeriv k S.limitResolvent y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent lambda) x) := by
    abel
  rw [hdecomp]
  calc
    ‖((_root_.iteratedDeriv k (F a) lambda) x -
          (_root_.iteratedDeriv k (F a) y.1) x) +
        ((_root_.iteratedDeriv k (F a) y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent y.1) x) +
        ((_root_.iteratedDeriv k S.limitResolvent y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent lambda) x)‖ ≤
      ‖(_root_.iteratedDeriv k (F a) lambda) x -
          (_root_.iteratedDeriv k (F a) y.1) x‖ +
      ‖(_root_.iteratedDeriv k (F a) y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent y.1) x‖ +
      ‖(_root_.iteratedDeriv k S.limitResolvent y.1) x -
          (_root_.iteratedDeriv k S.limitResolvent lambda) x‖ := by
        exact le_trans (norm_add_le _ _)
          (add_le_add (norm_add_le _ _) le_rfl)
    _ < epsilon := by
      have hcenterSmall := ha y hyt
      linarith

/-- Every finite Taylor jet converges strongly and uniformly on a compact
subgap spectral set. -/
theorem iteratedDeriv_tendsto_uniformOn_compact_apply_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (x : E) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        ‖(_root_.iteratedDeriv k (F a) lambda) x -
          (_root_.iteratedDeriv k S.limitResolvent lambda) x‖ < epsilon := by
  intro epsilon hepsilon
  induction order with
  | zero =>
      have hzero := S.iteratedDeriv_tendsto_uniformOn_compact_apply
        B L hLgap hLresolvent 0 K hKcompact hKu hu x epsilon hepsilon
      filter_upwards [hzero] with a ha
      intro k hk lambda hlambda
      have hk0 : k = 0 := by omega
      subst hk0
      exact ha lambda hlambda
  | succ order ih =>
      have htop := S.iteratedDeriv_tendsto_uniformOn_compact_apply
        B L hLgap hLresolvent (Nat.succ order) K hKcompact hKu hu x
        epsilon hepsilon
      filter_upwards [ih, htop] with a ha htopa
      intro k hk lambda hlambda
      by_cases hkle : k ≤ order
      · exact ha k hkle lambda hlambda
      · have hkeq : k = Nat.succ order := by omega
        subst hkeq
        exact htopa lambda hlambda

variable {𝕜 : Type*}
variable [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]

/-- A continuous linear observable preserves compact-uniform strong convergence
of one Taylor-jet level.  Matrix elements are obtained by choosing a Riesz
functional. -/
theorem iteratedDeriv_tendsto_uniformOn_compact_apply_continuousLinearMap
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (ell : E →L[ℝ] 𝕜)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (x : E) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖ell ((_root_.iteratedDeriv k (F a) lambda) x) -
          ell ((_root_.iteratedDeriv k S.limitResolvent lambda) x)‖ < epsilon := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / (‖ell‖ + 1)
  have hell1 : 0 < ‖ell‖ + 1 := by positivity
  have heta : 0 < eta := div_pos hepsilon hell1
  have hvec := S.iteratedDeriv_tendsto_uniformOn_compact_apply
    B L hLgap hLresolvent k K hKcompact hKu hu x eta heta
  filter_upwards [hvec] with a ha
  intro lambda hlambda
  have happly := ha lambda hlambda
  calc
    ‖ell ((_root_.iteratedDeriv k (F a) lambda) x) -
        ell ((_root_.iteratedDeriv k S.limitResolvent lambda) x)‖ =
      ‖ell (((_root_.iteratedDeriv k (F a) lambda) x) -
        ((_root_.iteratedDeriv k S.limitResolvent lambda) x))‖ := by
        rw [map_sub]
    _ ≤ ‖ell‖ *
        ‖((_root_.iteratedDeriv k (F a) lambda) x) -
          ((_root_.iteratedDeriv k S.limitResolvent lambda) x)‖ :=
      ell.le_opNorm _
    _ ≤ ‖ell‖ * eta :=
      mul_le_mul_of_nonneg_left (le_of_lt happly) (norm_nonneg ell)
    _ < epsilon := by
      have hratio : ‖ell‖ / (‖ell‖ + 1) < 1 :=
        (div_lt_one hell1).2 (lt_add_one ‖ell‖)
      calc
        ‖ell‖ * eta = epsilon * (‖ell‖ / (‖ell‖ + 1)) := by
          dsimp [eta]
          field_simp [ne_of_gt hell1]
        _ < epsilon * 1 := mul_lt_mul_of_pos_left hratio hepsilon
        _ = epsilon := mul_one epsilon

/-- A continuous linear observable preserves compact-uniform convergence of a
whole finite Taylor jet. -/
theorem iteratedDeriv_tendsto_uniformOn_compact_apply_continuousLinearMap_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (ell : E →L[ℝ] 𝕜)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (x : E) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        ‖ell ((_root_.iteratedDeriv k (F a) lambda) x) -
          ell ((_root_.iteratedDeriv k S.limitResolvent lambda) x)‖ < epsilon := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / (‖ell‖ + 1)
  have hell1 : 0 < ‖ell‖ + 1 := by positivity
  have heta : 0 < eta := div_pos hepsilon hell1
  have hvec := S.iteratedDeriv_tendsto_uniformOn_compact_apply_jet
    B L hLgap hLresolvent order K hKcompact hKu hu x eta heta
  filter_upwards [hvec] with a ha
  intro k hk lambda hlambda
  have happly := ha k hk lambda hlambda
  calc
    ‖ell ((_root_.iteratedDeriv k (F a) lambda) x) -
        ell ((_root_.iteratedDeriv k S.limitResolvent lambda) x)‖ =
      ‖ell (((_root_.iteratedDeriv k (F a) lambda) x) -
        ((_root_.iteratedDeriv k S.limitResolvent lambda) x))‖ := by
        rw [map_sub]
    _ ≤ ‖ell‖ *
        ‖((_root_.iteratedDeriv k (F a) lambda) x) -
          ((_root_.iteratedDeriv k S.limitResolvent lambda) x)‖ :=
      ell.le_opNorm _
    _ ≤ ‖ell‖ * eta :=
      mul_le_mul_of_nonneg_left (le_of_lt happly) (norm_nonneg ell)
    _ < epsilon := by
      have hratio : ‖ell‖ / (‖ell‖ + 1) < 1 :=
        (div_lt_one hell1).2 (lt_add_one ‖ell‖)
      calc
        ‖ell‖ * eta = epsilon * (‖ell‖ / (‖ell‖ + 1)) := by
          dsimp [eta]
          field_simp [ne_of_gt hell1]
        _ < epsilon * 1 := mul_lt_mul_of_pos_left hratio hepsilon
        _ = epsilon := mul_one epsilon

/-- The closed-parameter-box Taylor partial-sum joint limit remains uniform
after applying any continuous linear observable. -/
theorem taylorPartialSum_tendsto_limitResolvent_apply_continuousLinearMap_uniform_parameterBox_of_joint
    {β : Type*} {l : Filter α} {gap : ℝ}
    {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (ell : E →L[ℝ] 𝕜)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (x : E) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖ell ((continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b)) x) -
          ell (S.limitResolvent mu x)‖ < epsilon := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / (‖ell‖ + 1)
  have hell1 : 0 < ‖ell‖ + 1 := by positivity
  have heta : 0 < eta := div_pos hepsilon hell1
  have hvec :=
    S.taylorPartialSum_tendsto_limitResolvent_apply_uniform_parameterBox_of_joint
      B L hLgap hLresolvent a degree ha hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt x eta heta
  filter_upwards [hvec] with b hb
  intro lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu
  have happly := hb lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu
  calc
    ‖ell ((continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b)) x) -
        ell (S.limitResolvent mu x)‖ =
      ‖ell ((continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b)) x -
        S.limitResolvent mu x)‖ := by
        rw [map_sub]
    _ ≤ ‖ell‖ *
        ‖(continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b)) x -
          S.limitResolvent mu x‖ := ell.le_opNorm _
    _ ≤ ‖ell‖ * eta :=
      mul_le_mul_of_nonneg_left (le_of_lt happly) (norm_nonneg ell)
    _ < epsilon := by
      have hratio : ‖ell‖ / (‖ell‖ + 1) < 1 :=
        (div_lt_one hell1).2 (lt_add_one ‖ell‖)
      calc
        ‖ell‖ * eta = epsilon * (‖ell‖ / (‖ell‖ + 1)) := by
          dsimp [eta]
          field_simp [ne_of_gt hell1]
        _ < epsilon * 1 := mul_lt_mul_of_pos_left hratio hepsilon
        _ = epsilon := mul_one epsilon

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
