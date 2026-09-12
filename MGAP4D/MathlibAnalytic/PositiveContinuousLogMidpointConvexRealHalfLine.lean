import MGAP4D.MathlibAnalytic.ContinuousMidpointConvexRealHalfLine
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Positive continuous multiplicative midpoint control implies log convexity

Let `f : ℝ → ℝ` be everywhere positive and continuous.  If on the nonnegative
half-line it satisfies

`f ((s+t)/2)^2 ≤ f s * f t`,

then `log ∘ f` satisfies the additive midpoint Jensen inequality.  Continuity
of `log ∘ f` and the generic compact-maximum theorem from the preceding
convexity layer therefore give full `ConvexOn ℝ (Set.Ici 0)`.

This is the zero-free real-analysis bridge used after positive regularization of
physical OS correlations.
-/

namespace MGAP4D

open Set

/-- A positive continuous function with the multiplicative midpoint inequality
on `Ici 0` has a convex logarithm there. -/
theorem convexOn_log_Ici_of_continuous_pos_midpoint_sq_le_mul
    (f : ℝ → ℝ)
    (hf : Continuous f)
    (hpos : ∀ x : ℝ, 0 < f x)
    (hmul : ∀ {s t : ℝ}, s ∈ Ici (0 : ℝ) → t ∈ Ici (0 : ℝ) →
      f ((s + t) / 2) ^ 2 ≤ f s * f t) :
    ConvexOn ℝ (Ici (0 : ℝ)) (fun x => Real.log (f x)) := by
  apply convexOn_Ici_of_continuous_midpoint
  · exact hf.log (fun x => (hpos x).ne')
  · intro s t hs ht
    have hsq := hmul hs ht
    have hmpos : 0 < f ((s + t) / 2) := hpos _
    have hspos : 0 < f s := hpos s
    have htpos : 0 < f t := hpos t
    have hlog :
        Real.log (f ((s + t) / 2) ^ 2) ≤
          Real.log (f s * f t) :=
      Real.log_le_log (by positivity) hsq
    rw [Real.log_pow, Real.log_mul hspos.ne' htpos.ne'] at hlog
    norm_num at hlog
    linarith

end MGAP4D
