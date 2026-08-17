import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Continuous midpoint convexity on the real half-line

This file isolates the real-analysis step that upgrades midpoint convexity to
full convexity.  The proof avoids an explicit dyadic approximation.

For a continuous midpoint-convex function `g` on `[0,1]` with nonpositive
endpoints, compactness gives a maximum point `m`.  If that maximum were
positive, then either `m ≤ 1/2` or `1/2 ≤ m`.  In the first case `m` is the
midpoint of `0` and `2m`; in the second it is the midpoint of `2m-1` and `1`.
Midpoint convexity and maximality therefore give `g m ≤ g m / 2`, a
contradiction.  Applying this maximum principle to the defect from the chord
joining two points yields the full Jensen inequality.
-/

namespace MGAP4D

open Set

/-- Maximum principle for a continuous midpoint-convex real function on the
unit interval with nonpositive endpoint values. -/
theorem continuous_midpointConvex_nonpos_Icc
    (g : ℝ → ℝ)
    (hg : Continuous g)
    (hmid : ∀ {s t : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      g ((s + t) / 2) ≤ (g s + g t) / 2)
    (h0 : g 0 ≤ 0) (h1 : g 1 ≤ 0) :
    ∀ u ∈ Icc (0 : ℝ) 1, g u ≤ 0 := by
  obtain ⟨m, hm, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨0, by simp⟩ hg.continuousOn
  intro u hu
  by_contra hu0
  have hupos : 0 < g u := lt_of_not_ge hu0
  have humax := hmax hu
  change g u ≤ g m at humax
  have hmpos : 0 < g m := lt_of_lt_of_le hupos humax
  rcases le_total m (1 / 2 : ℝ) with hmhalf | hhalfm
  · have h2m : 2 * m ∈ Icc (0 : ℝ) 1 := by
      constructor
      · nlinarith [hm.1]
      · nlinarith
    have hmid' := hmid (show (0 : ℝ) ∈ Icc 0 1 by simp) h2m
    have h2max := hmax h2m
    change g (2 * m) ≤ g m at h2max
    have harg : ((0 : ℝ) + 2 * m) / 2 = m := by ring
    rw [harg] at hmid'
    nlinarith
  · have h2m1 : 2 * m - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith [hm.2]
    have hmid' := hmid h2m1 (show (1 : ℝ) ∈ Icc 0 1 by simp)
    have h2max := hmax h2m1
    change g (2 * m - 1) ≤ g m at h2max
    have harg : ((2 * m - 1) + 1) / 2 = m := by ring
    rw [harg] at hmid'
    nlinarith

/-- A continuous real function that satisfies the midpoint Jensen inequality on
`Ici 0` is fully convex there. -/
theorem convexOn_Ici_of_continuous_midpoint
    (f : ℝ → ℝ)
    (hf : Continuous f)
    (hmid : ∀ {s t : ℝ}, s ∈ Ici (0 : ℝ) → t ∈ Ici (0 : ℝ) →
      f ((s + t) / 2) ≤ (f s + f t) / 2) :
    ConvexOn ℝ (Ici (0 : ℝ)) f := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  let p : ℝ → ℝ := fun r => r * x + (1 - r) * y
  let ell : ℝ → ℝ := fun r => r * f x + (1 - r) * f y
  let g : ℝ → ℝ := fun r => f (p r) - ell r
  have hg : Continuous g := by
    dsimp [g, p, ell]
    fun_prop
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hgmid : ∀ {s t : ℝ}, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      g ((s + t) / 2) ≤ (g s + g t) / 2 := by
    intro s t hs ht
    have hps : p s ∈ Ici (0 : ℝ) := by
      dsimp [p]
      exact add_nonneg
        (mul_nonneg hs.1 hx0)
        (mul_nonneg (sub_nonneg.mpr hs.2) hy0)
    have hpt : p t ∈ Ici (0 : ℝ) := by
      dsimp [p]
      exact add_nonneg
        (mul_nonneg ht.1 hx0)
        (mul_nonneg (sub_nonneg.mpr ht.2) hy0)
    have h := hmid hps hpt
    have hp : p ((s + t) / 2) = (p s + p t) / 2 := by
      dsimp [p]
      ring
    have hell : ell ((s + t) / 2) = (ell s + ell t) / 2 := by
      dsimp [ell]
      ring
    dsimp [g]
    rw [hp, hell]
    linarith
  have hg0 : g 0 ≤ 0 := by
    dsimp [g, p, ell]
    simp
  have hg1 : g 1 ≤ 0 := by
    dsimp [g, p, ell]
    simp
  have ha1 : a ≤ 1 := by linarith
  have hga := continuous_midpointConvex_nonpos_Icc
    g hg hgmid hg0 hg1 a ⟨ha, ha1⟩
  have hba : 1 - a = b := by linarith
  dsimp [g, p, ell] at hga
  rw [hba] at hga
  simpa only [smul_eq_mul, sub_nonpos] using hga

end MGAP4D
