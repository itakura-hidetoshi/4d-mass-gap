import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachCore
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The finite-dimensional input space carrying a base resolvent family, an
endpoint resolvent family, and the complete finite operator-direction family. -/
abbrev ContinuousLinearMapJointTaylorDysonRemainderInput
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (taylorOrder m : ℕ) :=
  ((Fin (taylorOrder + 1) → (V →L[ℝ] V)) ×
    (Fin (taylorOrder + 1) → (V →L[ℝ] V))) ×
      (Fin m → (V →L[ℝ] V))

/-- Constructor for the complete remainder input. -/
def continuousLinearMapJointTaylorDysonRemainderInput
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {taylorOrder m : ℕ}
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (H : Fin m → (V →L[ℝ] V)) :
    ContinuousLinearMapJointTaylorDysonRemainderInput V taylorOrder m :=
  ((Rbase, Rend), H)

/-- Uniform convergence in a finite-dimensional normed space passes through
any continuous observable, uniformly over an arbitrary index set. -/
theorem finiteDimensional_continuousObservable_tendsto_uniform
    {α ι X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter α} {s : Set ι}
    (A : α → ι → X) (A0 : ι → X)
    (Phi : X → Y) (hPhi : Continuous Phi)
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s,
        ‖Phi (A a i) - Phi (A0 i)‖ < epsilon := by
  intro epsilon hepsilon
  let C : Set X := Metric.closedBall 0 (R + 1)
  have hCcompact : IsCompact C := isCompact_closedBall 0 (R + 1)
  have hUniform : UniformContinuousOn Phi C :=
    hCcompact.uniformContinuousOn_of_continuous hPhi.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp hUniform) epsilon hepsilon with
    ⟨delta, hdelta, hmodulus⟩
  let eta : ℝ := min delta 1
  have heta : 0 < eta := lt_min hdelta zero_lt_one
  filter_upwards [hA eta heta] with a ha
  intro i hi
  have hdiffDelta : ‖A a i - A0 i‖ < delta :=
    lt_of_lt_of_le (ha i hi) (min_le_left delta 1)
  have hdiffOne : ‖A a i - A0 i‖ < 1 :=
    lt_of_lt_of_le (ha i hi) (min_le_right delta 1)
  have hA0C : A0 i ∈ C := by
    have hnorm : ‖A0 i‖ ≤ R + 1 :=
      (hA0 i hi).trans (by linarith [hR])
    simpa [C, Metric.mem_closedBall, dist_zero_right] using hnorm
  have hAnorm : ‖A a i‖ ≤ R + 1 := by
    calc
      ‖A a i‖ = ‖A a i - A0 i + A0 i‖ := by rw [sub_add_cancel]
      _ ≤ ‖A a i - A0 i‖ + ‖A0 i‖ := norm_add_le _ _
      _ ≤ 1 + R := add_le_add (le_of_lt hdiffOne) (hA0 i hi)
      _ = R + 1 := by ring
  have hAC : A a i ∈ C := by
    simpa [C, Metric.mem_closedBall, dist_zero_right] using hAnorm
  have hdist : dist (A a i) (A0 i) < delta := by
    simpa [dist_eq_norm] using hdiffDelta
  have hout := hmodulus (A a i) hAC (A0 i) hA0C hdist
  simpa [dist_eq_norm] using hout

/-- Componentwise uniform convergence of the two resolvent families and
ordinary convergence of the finite direction family combine into uniform
convergence in the complete finite-dimensional input norm. -/
theorem continuousLinearMapJointTaylorDysonRemainderInput_tendsto_uniform_of_components
    {α ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter α} {s : Set ι} {taylorOrder m : ℕ}
    (Rbase : α → ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (Rbase0 : ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (Rend : α → ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (Rend0 : ι → Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hbase : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖Rbase a i - Rbase0 i‖ < eta)
    (hend : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖Rend a i - Rend0 i‖ < eta)
    (hH : Tendsto H l (𝓝 H0)) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderInput
          (Rbase a i) (Rend a i) (H a) -
        continuousLinearMapJointTaylorDysonRemainderInput
          (Rbase0 i) (Rend0 i) H0‖ < eta := by
  intro eta heta
  have hHeta : ∀ᶠ a in l, ‖H a - H0‖ < eta := by
    rw [Metric.tendsto_nhds] at hH
    simpa [dist_eq_norm] using hH eta heta
  filter_upwards [hbase eta heta, hend eta heta, hHeta] with a ha hb hc
  intro i hi
  rw [← dist_eq_norm]
  simpa [continuousLinearMapJointTaylorDysonRemainderInput,
    Prod.dist_eq, dist_eq_norm, max_lt_iff] using
    And.intro (And.intro (ha i hi) (hb i hi)) hc

/-- A continuous finite-dimensional remainder observable transfers uniform
convergence of complete remainder inputs to uniform convergence in the actual
remainder-rectangle Banach norm. -/
theorem finiteDimensional_jointTaylorDysonRemainderTailRectangularJet_tendsto_uniform
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ)
    (X : α → ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (X0 : ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (R : ℝ) (hR : 0 ≤ R)
    (hX0 : ∀ i ∈ s, ‖X0 i‖ ≤ R)
    (hX : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖X a i - X0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m (X a i).2 ds h
            (X a i).1.1 (X a i).1.2 -
        continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
          baseOrder taylorOrder tailOrder m (X0 i).2 ds h
            (X0 i).1.1 (X0 i).1.2‖ < epsilon := by
  let Phi := fun x : ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m =>
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
      baseOrder taylorOrder tailOrder m x.2 ds h x.1.1 x.1.2
  have hPhi : Continuous Phi := by
    simpa [Phi] using
      continuous_continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        (V := V) baseOrder taylorOrder tailOrder m ds h
  exact finiteDimensional_continuousObservable_tendsto_uniform
    X X0 Phi hPhi R hR hX0 hX

/-- The same complete-input transfer holds for every arbitrary Banach-valued
continuous-linear observation of the exact remainder rectangle. -/
theorem finiteDimensional_jointTaylorDysonRemainderTailResponseRectangularJet_tendsto_uniform
    {α ι V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {l : Filter α} {s : Set ι}
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ)
    (X : α → ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (X0 : ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (R : ℝ) (hR : 0 ≤ R)
    (hX0 : ∀ i ∈ s, ‖X0 i‖ ≤ R)
    (hX : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖X a i - X0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m (X a i).2 ds h
            (X a i).1.1 (X a i).1.2 -
        continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          φ baseOrder taylorOrder tailOrder m (X0 i).2 ds h
            (X0 i).1.1 (X0 i).1.2‖ < epsilon := by
  let Phi := fun x : ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m =>
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
      φ baseOrder taylorOrder tailOrder m x.2 ds h x.1.1 x.1.2
  have hPhi : Continuous Phi := by
    simpa [Phi] using
      continuous_continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ baseOrder taylorOrder tailOrder m ds h
  exact finiteDimensional_continuousObservable_tendsto_uniform
    X X0 Phi hPhi R hR hX0 hX

/-- Basis-independent traces inherit the complete finite-dimensional remainder
input transfer in the true finite-product norm. -/
theorem finiteDimensional_jointTaylorDysonRemainderTailTraceRectangularJet_tendsto_uniform
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (baseOrder taylorOrder tailOrder m : ℕ)
    (ds : ℝ) (h : Fin m → ℝ)
    (X : α → ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (X0 : ι → ContinuousLinearMapJointTaylorDysonRemainderInput
      V taylorOrder m)
    (R : ℝ) (hR : 0 ≤ R)
    (hX0 : ∀ i ∈ s, ‖X0 i‖ ≤ R)
    (hX : ∀ eta : ℝ, 0 < eta → ∀ᶠ a in l, ∀ i ∈ s,
      ‖X a i - X0 i‖ < eta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ i ∈ s,
      ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m (X a i).2 ds h
            (X a i).1.1 (X a i).1.2 -
        continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
          V baseOrder taylorOrder tailOrder m (X0 i).2 ds h
            (X0 i).1.1 (X0 i).1.2‖ < epsilon := by
  simpa [continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies] using
    finiteDimensional_jointTaylorDysonRemainderTailResponseRectangularJet_tendsto_uniform
      (continuousLinearMapTrace (V := V)) baseOrder taylorOrder tailOrder m
      ds h X X0 R hR hX0 hX

end MathlibAnalytic
end MGAP4D
