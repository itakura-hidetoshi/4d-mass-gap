import MGAP4D.MathlibAnalytic.ContinuousLinearMapBelowGapResolventFamily
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

/-- Filter-indexed Taylor strong-limit data on one common open below-gap
half-line.  The domain restriction is essential for proof-indexed resolvents:
no differentiability assertion is made at the spectral threshold itself. -/
structure ContinuousLinearMapOpenTaylorStrongLimitData
    {α E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : Filter α) (gap : ℝ)
    (F : α → ℝ → E →L[ℝ] E) where
  limitResolvent : ℝ → E →L[ℝ] E
  value_tendsto_apply : ∀ {mu : ℝ}, mu < gap → ∀ x : E,
    Tendsto (fun a => F a mu x) l (𝓝 (limitResolvent mu x))
  iteratedDeriv_tendsto_apply : ∀ k : ℕ, ∀ {lambda : ℝ}, lambda < gap →
    ∀ x : E,
      Tendsto (fun a => (_root_.iteratedDeriv k (F a) lambda) x) l
        (𝓝 ((_root_.iteratedDeriv k limitResolvent lambda) x))

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact factorial derivative identities and strong convergence of every
finite resolvent power construct all-order Taylor strong-limit data on the
common open half-line. -/
noncomputable def of_resolventPowers
    {l : Filter α} {gap : ℝ}
    {F : α → ℝ → E →L[ℝ] E} {R : ℝ → E →L[ℝ] E}
    (hValue : ∀ {mu : ℝ}, mu < gap → ∀ x : E,
      Tendsto (fun a => F a mu x) l (𝓝 (R mu x)))
    (hPower : ∀ k : ℕ, ∀ {lambda : ℝ}, lambda < gap → ∀ x : E,
      Tendsto (fun a => ((F a lambda) ^ (k + 1)) x) l
        (𝓝 (((R lambda) ^ (k + 1)) x)))
    (hDerivF : ∀ a : α, ∀ k : ℕ, ∀ {lambda : ℝ}, lambda < gap →
      _root_.iteratedDeriv k (F a) lambda =
        (k.factorial : ℝ) • (F a lambda) ^ (k + 1))
    (hDerivR : ∀ k : ℕ, ∀ {lambda : ℝ}, lambda < gap →
      _root_.iteratedDeriv k R lambda =
        (k.factorial : ℝ) • (R lambda) ^ (k + 1)) :
    ContinuousLinearMapOpenTaylorStrongLimitData l gap F where
  limitResolvent := R
  value_tendsto_apply := by
    intro mu hmu x
    exact hValue (mu := mu) hmu x
  iteratedDeriv_tendsto_apply := by
    intro k lambda hlambda x
    have hp :=
      (hPower k (lambda := lambda) hlambda x).const_smul
        (k.factorial : ℝ)
    rw [hDerivR k (lambda := lambda) hlambda]
    have hsource :
        (fun a => (_root_.iteratedDeriv k (F a) lambda) x) =
          (fun a => (k.factorial : ℝ) • (((F a lambda) ^ (k + 1)) x)) := by
      funext a
      rw [hDerivF a k (lambda := lambda) hlambda]
      rfl
    rw [hsource]
    simpa only [ContinuousLinearMap.smul_apply] using hp

/-- Every finite Taylor polynomial term converges strongly to the corresponding
term of the limit resolvent at any below-gap center and evaluation point. -/
theorem taylorTerm_tendsto_apply
    {l : Filter α} {gap : ℝ}
    {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < gap)
    (mu : ℝ) (x : E) :
    Tendsto
      (fun a =>
        (((mu - lambda) ^ k / (k.factorial : ℝ)) •
          (_root_.iteratedDeriv k (F a) lambda)) x)
      l
      (𝓝
        ((((mu - lambda) ^ k / (k.factorial : ℝ)) •
          (_root_.iteratedDeriv k S.limitResolvent lambda)) x)) := by
  have h :=
    S.iteratedDeriv_tendsto_apply k (lambda := lambda) hlambda x
  simpa only [ContinuousLinearMap.smul_apply] using
    h.const_smul ((mu - lambda) ^ k / (k.factorial : ℝ))

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
