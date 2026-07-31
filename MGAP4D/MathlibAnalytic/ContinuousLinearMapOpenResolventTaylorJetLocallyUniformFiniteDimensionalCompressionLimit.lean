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

/-- A basis estimate for the norm of a finite-dimensional compression.
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
      ‖basisValuesToContinuousLinearMap v‖ * ‖Q‖ *
        ‖fun i => (A - B) (J (v i))‖ := by
  have hpi :
      ‖fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ ≤
        ‖Q‖ * ‖fun i => (A - B) (J (v i))‖ := by
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (norm_nonneg Q)
        (norm_nonneg (fun i => (A - B) (J (v i)))))).2
    intro i
    calc
      ‖(continuousLinearMapCompression J Q A -
          continuousLinearMapCompression J Q B) (v i)‖ =
          ‖Q ((A - B) (J (v i)))‖ := by
            simp [continuousLinearMapCompression]
      _ ≤ ‖Q‖ * ‖(A - B) (J (v i))‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * ‖fun j => (A - B) (J (v j))‖ :=
        mul_le_mul_of_nonneg_left
          (norm_apply_le_norm (fun j => (A - B) (J (v j))) i)
          (norm_nonneg Q)
  calc
    ‖continuousLinearMapCompression J Q A -
        continuousLinearMapCompression J Q B‖ =
      ‖basisValuesToContinuousLinearMap v
        (fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i))‖ := by
        rw [basisValuesToContinuousLinearMap_reconstruct]
    _ ≤ ‖basisValuesToContinuousLinearMap v‖ *
        ‖fun i =>
          (continuousLinearMapCompression J Q A -
            continuousLinearMapCompression J Q B) (v i)‖ :=
      (basisValuesToContinuousLinearMap v).le_opNorm _
    _ ≤ ‖basisValuesToContinuousLinearMap v‖ *
        (‖Q‖ * ‖fun i => (A - B) (J (v i))‖) :=
      mul_le_mul_of_nonneg_left hpi
        (norm_nonneg (basisValuesToContinuousLinearMap v))
    _ = ‖basisValuesToContinuousLinearMap v‖ * ‖Q‖ *
        ‖fun i => (A - B) (J (v i))‖ := by ring

/-- Coordinatewise control on one finite basis gives a strict operator-norm
bound for the compressed difference. -/
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
            ((‖basisValuesToContinuousLinearMap v‖ + 1) *
              (‖Q‖ + 1))) :
    ‖continuousLinearMapCompression J Q A -
        continuousLinearMapCompression J Q B‖ < epsilon := by
  let eta : ℝ :=
    epsilon /
      ((‖basisValuesToContinuousLinearMap v‖ + 1) * (‖Q‖ + 1))
  have hc1 : 0 < ‖basisValuesToContinuousLinearMap v‖ + 1 := by positivity
  have hq1 : 0 < ‖Q‖ + 1 := by positivity
  have heta : 0 < eta := div_pos hepsilon (mul_pos hc1 hq1)
  have hpi :
      ‖fun i => (A - B) (J (v i))‖ < eta := by
    apply (pi_norm_lt_iff heta).2
    intro i
    simpa [eta] using h i
  have hcoef :
      ‖basisValuesToContinuousLinearMap v‖ * ‖Q‖ ≤
        (‖basisValuesToContinuousLinearMap v‖ + 1) * (‖Q‖ + 1) := by
    nlinarith [norm_nonneg (basisValuesToContinuousLinearMap v), norm_nonneg Q]
  calc
    ‖continuousLinearMapCompression J Q A -
        continuousLinearMapCompression J Q B‖ ≤
      ‖basisValuesToContinuousLinearMap v‖ * ‖Q‖ *
        ‖fun i => (A - B) (J (v i))‖ :=
      continuousLinearMapCompression_sub_norm_le_basis v J Q A B
    _ ≤
      ((‖basisValuesToContinuousLinearMap v‖ + 1) * (‖Q‖ + 1)) *
        ‖fun i => (A - B) (J (v i))‖ :=
      mul_le_mul_of_nonneg_right hcoef
        (norm_nonneg (fun i => (A - B) (J (v i))))
    _ <
      ((‖basisValuesToContinuousLinearMap v‖ + 1) * (‖Q‖ + 1)) * eta :=
      mul_lt_mul_of_pos_left hpi (mul_pos hc1 hq1)
    _ = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hc1, ne_of_gt hq1]

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
      ((‖basisValuesToContinuousLinearMap v‖ + 1) * (‖Q‖ + 1))
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
      ((‖basisValuesToContinuousLinearMap v‖ + 1) * (‖Q‖ + 1))
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
