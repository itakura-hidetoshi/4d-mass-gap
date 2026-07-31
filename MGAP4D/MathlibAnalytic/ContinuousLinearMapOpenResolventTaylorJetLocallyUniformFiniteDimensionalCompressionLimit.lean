import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJetLocallyUniformMatrixElementLimit
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorStrongLimitUpgradeBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Compress an endomorphism of `E` through a finite-dimensional test space.
No finite-dimensional hypothesis is needed for the definition itself. -/
def continuousLinearMapCompression
    {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (A : E →L[ℝ] E) :
    V →L[ℝ] V :=
  Q.comp (A.comp J)

@[simp]
theorem continuousLinearMapCompression_apply
    {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (A : E →L[ℝ] E)
    (x : V) :
    continuousLinearMapCompression J Q A x = Q (A (J x)) := rfl

/-- A finite basis controls the norm of a compressed operator difference.
The ambient space `E` may remain infinite dimensional. -/
theorem continuousLinearMapCompression_sub_norm_le_basis
    {ι E V : Type*}
    [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (v : Basis ι ℝ V)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (A B : E →L[ℝ] E) :
    ‖continuousLinearMapCompression J Q A -
        continuousLinearMapCompression J Q B‖ ≤
      ‖basisValuesToContinuousLinearMap (F := V) v‖ *
        ‖fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ := by
  calc
    ‖continuousLinearMapCompression J Q A -
        continuousLinearMapCompression J Q B‖ =
      ‖basisValuesToContinuousLinearMap (F := V) v
        (fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i))‖ := by
        rw [basisValuesToContinuousLinearMap_reconstruct]
    _ ≤ ‖basisValuesToContinuousLinearMap (F := V) v‖ *
        ‖fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ :=
      (basisValuesToContinuousLinearMap (F := V) v).le_opNorm _

/-- Coordinatewise control before compression on one finite basis gives a
strict operator-norm bound for the compressed difference. -/
theorem continuousLinearMapCompression_sub_norm_lt_of_apply_basis
    {ι E V : Type*}
    [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (v : Basis ι ℝ V)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (A B : E →L[ℝ] E)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (h :
      ∀ i,
        ‖(A - B) (J (v i))‖ <
          epsilon /
            ((‖basisValuesToContinuousLinearMap (F := V) v‖ + 1) *
              (‖Q‖ + 1))) :
    ‖continuousLinearMapCompression J Q A -
        continuousLinearMapCompression J Q B‖ < epsilon := by
  let c : ℝ := ‖basisValuesToContinuousLinearMap (F := V) v‖
  let q : ℝ := ‖Q‖
  let eta : ℝ := epsilon / ((c + 1) * (q + 1))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hc1 : 0 < c + 1 := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon (mul_pos hc1 hq1)
  have hcompressed :
      ∀ i,
        ‖(continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ <
          epsilon / (c + 1) := by
    intro i
    have hraw : ‖(A - B) (J (v i))‖ < eta := by
      simpa [c, q, eta] using h i
    calc
      ‖(continuousLinearMapCompression J Q A -
          continuousLinearMapCompression J Q B) (v i)‖ =
          ‖Q ((A - B) (J (v i)))‖ := by
            simp [continuousLinearMapCompression]
      _ ≤ q * ‖(A - B) (J (v i))‖ := by
        simpa [q] using Q.le_opNorm ((A - B) (J (v i)))
      _ ≤ (q + 1) * ‖(A - B) (J (v i))‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (q + 1) * eta := mul_lt_mul_of_pos_left hraw hq1
      _ = epsilon / (c + 1) := by
        dsimp [eta]
        field_simp [ne_of_gt hc1, ne_of_gt hq1]
  have hpi :
      ‖fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ <
        epsilon / (c + 1) := by
    apply (pi_norm_lt_iff (div_pos hepsilon hc1)).2
    exact hcompressed
  calc
    ‖continuousLinearMapCompression J Q A -
        continuousLinearMapCompression J Q B‖ ≤
      c *
        ‖fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ := by
      simpa [c] using
        continuousLinearMapCompression_sub_norm_le_basis v J Q A B
    _ ≤ (c + 1) *
        ‖fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (c + 1) * (epsilon / (c + 1)) :=
      mul_lt_mul_of_pos_left hpi hc1
    _ = epsilon := by
      field_simp [ne_of_gt hc1]

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Every fixed Taylor-jet level converges in operator norm after compression
through an arbitrary finite-dimensional test space. -/
theorem iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda) -
          continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)‖ < epsilon := by
  intro epsilon hepsilon
  let v := Module.finBasis ℝ V
  let eta : ℝ :=
    epsilon /
      ((‖basisValuesToContinuousLinearMap (F := V) v‖ + 1) * (‖Q‖ + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hbasis :
      ∀ i : Fin (finrank ℝ V),
        ∀ᶠ a in l, ∀ lambda ∈ K,
          ‖(_root_.iteratedDeriv k (F a) lambda) (J (v i)) -
            (_root_.iteratedDeriv k S.limitResolvent lambda) (J (v i))‖ <
              eta := by
    intro i
    exact
      S.iteratedDeriv_tendsto_uniformOn_compact_apply
        B L hLgap hLresolvent k K hKcompact hKu hu (J (v i)) eta heta
  have hfinite :
      ∀ᶠ a in l, ∀ i : Fin (finrank ℝ V), ∀ lambda ∈ K,
        ‖(_root_.iteratedDeriv k (F a) lambda) (J (v i)) -
          (_root_.iteratedDeriv k S.limitResolvent lambda) (J (v i))‖ <
            eta := by
    change {a | ∀ i : Fin (finrank ℝ V), ∀ lambda ∈ K,
      ‖(_root_.iteratedDeriv k (F a) lambda) (J (v i)) -
        (_root_.iteratedDeriv k S.limitResolvent lambda) (J (v i))‖ <
          eta} ∈ l
    rw [show {a | ∀ i : Fin (finrank ℝ V), ∀ lambda ∈ K,
        ‖(_root_.iteratedDeriv k (F a) lambda) (J (v i)) -
          (_root_.iteratedDeriv k S.limitResolvent lambda) (J (v i))‖ <
            eta} =
      ⋂ i ∈ Finset.univ,
        {a | ∀ lambda ∈ K,
          ‖(_root_.iteratedDeriv k (F a) lambda) (J (v i)) -
            (_root_.iteratedDeriv k S.limitResolvent lambda) (J (v i))‖ <
              eta} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem Finset.univ).2 fun i hi => hbasis i
  filter_upwards [hfinite] with a ha
  intro lambda hlambda
  apply continuousLinearMapCompression_sub_norm_lt_of_apply_basis
    v J Q
    (_root_.iteratedDeriv k (F a) lambda)
    (_root_.iteratedDeriv k S.limitResolvent lambda)
    hepsilon
  intro i
  simpa [eta] using ha i lambda hlambda

/-- A whole finite Taylor jet converges in compressed operator norm uniformly
on each compact strict subgap set. -/
theorem iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        ‖continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda) -
          continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)‖ < epsilon := by
  intro epsilon hepsilon
  have hk :
      ∀ k ∈ Finset.range (order + 1),
        ∀ᶠ a in l, ∀ lambda ∈ K,
          ‖continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda) -
            continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)‖ < epsilon := by
    intro k hk
    exact
      S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
        B L hLgap hLresolvent J Q k K hKcompact hKu hu epsilon hepsilon
  have hfinite :
      ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
        ‖continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda) -
          continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)‖ < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
      ‖continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda) -
        continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)‖ < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K,
        ‖continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda) -
          continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)‖ < epsilon} =
      ⋂ k ∈ Finset.range (order + 1),
        {a | ∀ lambda ∈ K,
          ‖continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda) -
            continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)‖ < epsilon} by
      ext a
      simp]
    exact
      (Filter.biInter_finset_mem (Finset.range (order + 1))).2
        fun k hk' => hk k hk'
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

/-- The rate-independent closed-parameter-box Taylor joint limit upgrades to
operator-norm convergence after every finite-dimensional compression. -/
theorem taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F (a b)) lambda mu (degree b)) -
          continuousLinearMapCompression J Q
            (S.limitResolvent mu)‖ < epsilon := by
  intro epsilon hepsilon
  let v := Module.finBasis ℝ V
  let eta : ℝ :=
    epsilon /
      ((‖basisValuesToContinuousLinearMap (F := V) v‖ + 1) * (‖Q‖ + 1))
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hbasis :
      ∀ i : Fin (finrank ℝ V),
        ∀ᶠ b in m, ∀ lambda r mu : ℝ,
          lambdaMin ≤ lambda → lambda ≤ lambdaMax →
          0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
          ‖(continuousLinearMapTaylorPartialSum
              (F (a b)) lambda mu (degree b)) (J (v i)) -
            S.limitResolvent mu (J (v i))‖ < eta := by
    intro i
    exact
      S.taylorPartialSum_tendsto_limitResolvent_apply_uniform_parameterBox_of_joint
        B L hLgap hLresolvent a degree ha hdegree
        hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt
        (J (v i)) eta heta
  have hfinite :
      ∀ᶠ b in m, ∀ i : Fin (finrank ℝ V), ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖(continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b)) (J (v i)) -
          S.limitResolvent mu (J (v i))‖ < eta := by
    change {b | ∀ i : Fin (finrank ℝ V), ∀ lambda r mu : ℝ,
      lambdaMin ≤ lambda → lambda ≤ lambdaMax →
      0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
      ‖(continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b)) (J (v i)) -
        S.limitResolvent mu (J (v i))‖ < eta} ∈ m
    rw [show {b | ∀ i : Fin (finrank ℝ V), ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖(continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b)) (J (v i)) -
          S.limitResolvent mu (J (v i))‖ < eta} =
      ⋂ i ∈ Finset.univ,
        {b | ∀ lambda r mu : ℝ,
          lambdaMin ≤ lambda → lambda ≤ lambdaMax →
          0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
          ‖(continuousLinearMapTaylorPartialSum
              (F (a b)) lambda mu (degree b)) (J (v i)) -
            S.limitResolvent mu (J (v i))‖ < eta} by
      ext b
      simp]
    exact (Filter.biInter_finset_mem Finset.univ).2 fun i hi => hbasis i
  filter_upwards [hfinite] with b hb
  intro lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu
  apply continuousLinearMapCompression_sub_norm_lt_of_apply_basis
    v J Q
    (continuousLinearMapTaylorPartialSum
      (F (a b)) lambda mu (degree b))
    (S.limitResolvent mu)
    hepsilon
  intro i
  simpa [eta] using
    hb i lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
