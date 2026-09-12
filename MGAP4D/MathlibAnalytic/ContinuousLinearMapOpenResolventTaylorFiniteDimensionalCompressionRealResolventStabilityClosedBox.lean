import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionCharacteristicDeterminantClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- For arbitrary joint time/Taylor-degree nets on a complete closed Taylor
box, a positive continuum determinant margin and a uniform continuum compressed
inverse bound give eventual unit stability, a uniform approximating inverse
bound, and operator-norm convergence of the true finite-dimensional real
resolvents. -/
theorem taylorPartialSum_realResolvent_finiteDimensionalCompression_eventually_stable_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      IsUnit (continuousLinearMapRealShift (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) ∧
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z ≤ 2 * (M + 1) ∧
      ‖continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z - continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z‖ < epsilon := by
  have hoperator : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ p ∈ {p | box.Contains p},
        ‖continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b)) -
          continuousLinearMapCompression J Q
              (S.limitResolvent p.target)‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree
        box.delta_le_gap box.lambda_bounds box.lambdaMax_lt_delta
        box.rMax_nonneg box.rMax_lt_margin eta heta
    filter_upwards [h] with b hb
    intro p hp
    exact hb p.center p.radius p.target
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  exact finiteDimensional_realResolvent_eventually_stable
    (l := m) (s := {p | box.Contains p})
    (fun b p => continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum
        (F (a b)) p.center p.target (degree b)))
    (fun p => continuousLinearMapCompression J Q
      (S.limitResolvent p.target))
    hoperator Z margin hmargin hlimitMargin M hM hlimitResolventNorm

/-- Operator-valued real resolvents converge uniformly on the complete closed
Taylor box for arbitrary joint time/Taylor-degree nets. -/
theorem taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z - continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z‖ < epsilon := by
  intro epsilon hepsilon
  have h := S.taylorPartialSum_realResolvent_finiteDimensionalCompression_eventually_stable_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q a degree ha hdegree box Z
    margin hmargin hlimitMargin M hM hlimitResolventNorm epsilon hepsilon
  filter_upwards [h] with b hb
  exact fun p hp z hz => (hb p hp z hz).2.2

/-- Every real spectral parameter in `Z` is eventually in the resolvent set of
all compressed Taylor partial sums on the whole closed box. -/
theorem taylorPartialSum_finiteDimensionalCompression_eventually_mem_realResolventSet_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      z ∈ resolventSet ℝ (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) := by
  have h := S.taylorPartialSum_realResolvent_finiteDimensionalCompression_eventually_stable_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q a degree ha hdegree box Z
    margin hmargin hlimitMargin M hM hlimitResolventNorm 1 zero_lt_one
  filter_upwards [h] with b hb
  intro p hp z hz
  exact continuousLinearMap_mem_real_resolventSet_of_isUnit _ _ (hb p hp z hz).1

/-- The whole real set `Z` is eventually excluded from the operator-norm
pseudospectrum of every compressed Taylor partial sum on the closed box. -/
theorem taylorPartialSum_finiteDimensionalCompression_eventually_not_mem_realPseudospectrum_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      z ∉ continuousLinearMapRealPseudospectrum (2 * (M + 1)) (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) := by
  have h := S.taylorPartialSum_realResolvent_finiteDimensionalCompression_eventually_stable_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q a degree ha hdegree box Z
    margin hmargin hlimitMargin M hM hlimitResolventNorm 1 zero_lt_one
  filter_upwards [h] with b hb
  intro p hp z hz
  exact continuousLinearMap_not_mem_realPseudospectrum_of_isUnit_of_norm_le
    (hb p hp z hz).1 (hb p hp z hz).2.1

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
