import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarActualFiniteDeficitMassCertificate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# P4-Q2-AJ2: strict finite contraction is NOT a uniform physical mass rate

AJ1 certified an explicit positive finite-volume Wilson excitation rate
m_n=(1-q_n)/a_n when q_n=||S_n-P_n||<1. The rate can nevertheless tend to
ZERO as the physical spacing a_n tends to zero.

This file formalizes the purely scalar *logical obstruction*:
for ANY sequence a_n>0 with a_n -> 0, the real positive factors
  q_n = exp(-(a_n)^2)
satisfy q_n<1 at every n, but their exact spacing-scaled logarithmic
rates are
  -log(q_n)/a_n = a_n -> 0.
No positive constant m can satisfy q_n ≤ exp(-m*a_n) for every n.

This is NOT a replacement Wilson transfer, posterior law, Gram matrix,
or a claim that genuine Wilson factors actually equal these scalar
examples. It proves why the true physical model must provide a new
uniform-in-volume spacing-scaled spectral estimate beyond compactness
and strict contraction. No axiom, sorry, admit, Dobrushin, or continuum
mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- An abstract strictly contractive scalar family at EVERY positive
spacing, even when no uniform physical-time rate exists. -/
theorem p4Q2AJ2_exp_neg_spacing_sq_strict
    (spacing : ℕ → ℝ) (hpos : ∀ n, 0 < spacing n) :
    ∀ n, 0 < Real.exp (-(spacing n)^2) ∧
      Real.exp (-(spacing n)^2) < 1 := by
  intro n
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_lt_one_iff]
  have hs : 0 < (spacing n)^2 := pow_pos (hpos n) 2
  linarith

/-- Its EXACT derived logarithmic mass rate equals the lattice spacing,
so it tends to zero as spacing goes to zero. -/
theorem p4Q2AJ2_exp_neg_spacing_sq_rate_eq
    (spacing : ℕ → ℝ) (hpos : ∀ n, 0 < spacing n)
    (n : ℕ) :
    -Real.log (Real.exp (-(spacing n)^2)) / spacing n =
      spacing n := by
  rw [Real.log_exp]
  have hs : spacing n ≠ 0 := (hpos n).ne'
  field_simp [hs] <;> ring

theorem p4Q2AJ2_exp_neg_spacing_sq_massRate_tendsto_zero
    (spacing : ℕ → ℝ) (hpos : ∀ n, 0 < spacing n)
    (hzero : Tendsto spacing atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ => -Real.log (Real.exp (-(spacing n)^2)) / spacing n)
      atTop (nhds 0) := by
  convert hzero using 1
  funext n
  exact p4Q2AJ2_exp_neg_spacing_sq_rate_eq spacing hpos n

/-- Genuine logical obstruction: q_n<1 alone cannot imply a common
strictly positive physical-time mass m, even when every q_n is positive.
No fake physical operator is introduced, only a scalar sequence that
disproves an otherwise invalid abstract implication. -/
theorem p4Q2AJ2_exp_neg_spacing_sq_no_uniform_mass
    (spacing : ℕ → ℝ) (hpos : ∀ n, 0 < spacing n)
    (hzero : Tendsto spacing atTop (nhds 0)) :
    ¬ ∃ mass : ℝ, 0 < mass ∧ ∀ n : ℕ,
      Real.exp (-(spacing n)^2) ≤
        Real.exp (-mass * spacing n) := by
  rintro ⟨mass, hmass, hUniform⟩
  have he : ∀ᶠ n : ℕ in atTop, spacing n < mass :=
    hzero.eventually_lt_const hmass
  obtain ⟨n, hn⟩ := he.exists
  have hExp :
      Real.exp (-(spacing n)^2) ≤
        Real.exp (-mass * spacing n) :=
    hUniform n
  have hArg : -(spacing n)^2 ≤ -mass * spacing n :=
    Real.exp_le_exp.mp hExp
  have hStrict : 0 < (mass - spacing n) * spacing n :=
    mul_pos (sub_pos.mpr hn) (hpos n)
  nlinarith

/-- The three statements together establish the precise negative
inference: strictness at every finite scale does not imply a
spacing-uniform rate. This is an abstract obstruction only. -/
theorem p4Q2AJ2_strictContraction_no_uniformMass_bundle
    (spacing : ℕ → ℝ) (hpos : ∀ n, 0 < spacing n)
    (hzero : Tendsto spacing atTop (nhds 0)) :
    (∀ n, 0 < Real.exp (-(spacing n)^2) ∧
      Real.exp (-(spacing n)^2) < 1) ∧
    Tendsto
      (fun n : ℕ => -Real.log (Real.exp (-(spacing n)^2)) / spacing n)
      atTop (nhds 0) ∧
    ¬ ∃ mass : ℝ, 0 < mass ∧ ∀ n : ℕ,
      Real.exp (-(spacing n)^2) ≤ Real.exp (-mass * spacing n) := by
  exact ⟨p4Q2AJ2_exp_neg_spacing_sq_strict spacing hpos,
    p4Q2AJ2_exp_neg_spacing_sq_massRate_tendsto_zero spacing hpos hzero,
    p4Q2AJ2_exp_neg_spacing_sq_no_uniform_mass spacing hpos hzero⟩

end
end MathlibAnalytic
end MGAP4D
