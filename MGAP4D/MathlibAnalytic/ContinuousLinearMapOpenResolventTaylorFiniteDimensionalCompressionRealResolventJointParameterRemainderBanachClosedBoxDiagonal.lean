import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterRemainderBanachClosedBox

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The arbitrary joint-net theorem is already the complete diagonal no-rate
statement: approximation time, Taylor degree, and direction-family motion have
no prescribed coupling rate. -/
theorem JointRemainderClosedBoxData.carrier_diagonal_noRate
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : JointRemainderClosedBoxData (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
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
          (closedBoxJointRemainderLimitBaseFamily D.J D.Q D.S.limitResolvent p z)
          (closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
            D.S.limitResolvent p z D.H0 D.ds D.h)‖ < epsilon :=
  D.carrier_tendsto baseOrder tailOrder epsilon hepsilon

/-- Banach-valued diagonal no-rate exact-remainder convergence. -/
theorem JointRemainderClosedBoxData.response_diagonal_noRate
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : JointRemainderClosedBoxData (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
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
          (closedBoxJointRemainderLimitBaseFamily D.J D.Q D.S.limitResolvent p z)
          (closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
            D.S.limitResolvent p z D.H0 D.ds D.h)‖ < epsilon :=
  D.response_tendsto φ baseOrder tailOrder epsilon hepsilon

/-- Basis-independent trace diagonal no-rate exact-remainder convergence. -/
theorem JointRemainderClosedBoxData.trace_diagonal_noRate
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    {n : Filter β} {directions : ℕ}
    (D : JointRemainderClosedBoxData (α := α) (β := β) (E := E) (V := V)
      (l := l) (gap := gap) (F := F) (n := n) directions)
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
          (closedBoxJointRemainderLimitBaseFamily D.J D.Q D.S.limitResolvent p z)
          (closedBoxJointRemainderLimitEndpointFamily D.J D.Q directions
            D.S.limitResolvent p z D.H0 D.ds D.h)‖ < epsilon :=
  D.trace_tendsto baseOrder tailOrder epsilon hepsilon

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
