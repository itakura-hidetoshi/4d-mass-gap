import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionContinuousSpectralObservablePackage
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The basis-independent real characteristic determinant profile
`z ↦ det (z I - A)` of a finite-dimensional continuous endomorphism. -/
def continuousLinearMapCharacteristicDeterminant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  (z • (1 : V →L[ℝ] V) - A).det

/-- The characteristic determinant profile is jointly continuous in the
operator and the real spectral parameter. -/
theorem continuous_continuousLinearMapCharacteristicDeterminant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    Continuous (fun p : (V →L[ℝ] V) × ℝ =>
      continuousLinearMapCharacteristicDeterminant p.1 p.2) := by
  unfold continuousLinearMapCharacteristicDeterminant
  exact ContinuousLinearMap.continuous_det.comp (by fun_prop)

/-- At every fixed real spectral parameter, the characteristic determinant is
continuous in operator norm. -/
theorem continuous_continuousLinearMapCharacteristicDeterminant_fixed
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (z : ℝ) :
    Continuous (fun A : V →L[ℝ] V =>
      continuousLinearMapCharacteristicDeterminant A z) := by
  exact continuous_continuousLinearMapCharacteristicDeterminant.comp (by fun_prop)

/-- A finite vector of characteristic determinant samples. -/
def continuousLinearMapCharacteristicDeterminantSampleJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {order : ℕ} (sample : Fin (order + 1) → ℝ)
    (A : V →L[ℝ] V) : Fin (order + 1) → ℝ :=
  fun j => continuousLinearMapCharacteristicDeterminant A (sample j)

/-- Every finite characteristic determinant sample jet is continuous in the
supremum norm. -/
theorem continuous_continuousLinearMapCharacteristicDeterminantSampleJet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    {order : ℕ} (sample : Fin (order + 1) → ℝ) :
    Continuous
      (continuousLinearMapCharacteristicDeterminantSampleJet (V := V) sample) := by
  unfold continuousLinearMapCharacteristicDeterminantSampleJet
  apply continuous_pi
  intro j
  exact continuous_continuousLinearMapCharacteristicDeterminant_fixed (sample j)

/-- Uniform convergence in a finite-dimensional normed space passes through a
jointly continuous observable uniformly over an additional compact real
parameter set. -/
theorem finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactRealParameter
    {α ι X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter α} {s : Set ι}
    (A : α → ι → X) (A0 : ι → X)
    (Phi : X → ℝ → Y)
    (hPhi : Continuous (fun p : X × ℝ => Phi p.1 p.2))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (K : Set ℝ) (hKcompact : IsCompact K) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ K,
        ‖Phi (A a i) z - Phi (A0 i) z‖ < epsilon := by
  intro epsilon hepsilon
  let C : Set X := Metric.closedBall 0 (R + 1)
  let D : Set (X × ℝ) := C ×ˢ K
  have hCcompact : IsCompact C := isCompact_closedBall 0 (R + 1)
  have hDcompact : IsCompact D := hCcompact.prod hKcompact
  have hUniform : UniformContinuousOn (fun p : X × ℝ => Phi p.1 p.2) D :=
    hDcompact.uniformContinuousOn_of_continuous hPhi.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp hUniform) epsilon hepsilon with
    ⟨delta, hdelta, hmodulus⟩
  let eta : ℝ := min delta 1
  have heta : 0 < eta := lt_min hdelta zero_lt_one
  have hApprox := hA eta heta
  filter_upwards [hApprox] with a ha
  intro i hi z hz
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
  have hpair0 : (A0 i, z) ∈ D := ⟨hA0C, hz⟩
  have hpair : (A a i, z) ∈ D := ⟨hAC, hz⟩
  have hdist : dist (A a i, z) (A0 i, z) < delta := by
    simpa [Prod.dist_eq, dist_eq_norm] using hdiffDelta
  have hout := hmodulus (A a i, z) hpair (A0 i, z) hpair0 hdist
  simpa [dist_eq_norm] using hout

/-- Uniform finite-dimensional operator convergence yields compact-uniform
convergence of the complete real characteristic determinant profile. -/
theorem finiteDimensional_characteristicDeterminant_tendsto_uniformOn_compactRealParameter
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (K : Set ℝ) (hKcompact : IsCompact K) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ K,
        |continuousLinearMapCharacteristicDeterminant (A a i) z -
          continuousLinearMapCharacteristicDeterminant (A0 i) z| < epsilon := by
  simpa [Real.norm_eq_abs] using
    finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactRealParameter
      A A0 continuousLinearMapCharacteristicDeterminant
      continuous_continuousLinearMapCharacteristicDeterminant
      R hR hA0 hA K hKcompact

/-- A positive uniform continuum margin for the characteristic determinant is
stable under sufficiently small uniform operator perturbations. -/
theorem finiteDimensional_characteristicDeterminant_eventually_abs_gt_half_margin
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (K : Set ℝ) (hKcompact : IsCompact K)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ K,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|) :
    ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ K,
      margin / 2 < |continuousLinearMapCharacteristicDeterminant (A a i) z| := by
  have hconv :=
    finiteDimensional_characteristicDeterminant_tendsto_uniformOn_compactRealParameter
      A A0 R hR hA0 hA K hKcompact (margin / 2) (half_pos hmargin)
  filter_upwards [hconv] with a ha
  intro i hi z hz
  let x := continuousLinearMapCharacteristicDeterminant (A a i) z
  let y := continuousLinearMapCharacteristicDeterminant (A0 i) z
  have hxy : |x - y| < margin / 2 := ha i hi z hz
  have hy : margin ≤ |y| := hlimitMargin i hi z hz
  have hyx : |y| ≤ |x - y| + |x| := by
    calc
      |y| = |(y - x) + x| := by ring_nf
      _ ≤ |y - x| + |x| := abs_add_le _ _
      _ = |x - y| + |x| := by rw [abs_sub_comm]
  linarith

/-- Under the same positive continuum margin, every approximating real
characteristic determinant is eventually nonzero on the whole parameter set. -/
theorem finiteDimensional_characteristicDeterminant_eventually_ne_zero
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (K : Set ℝ) (hKcompact : IsCompact K)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ K,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|) :
    ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ K,
      continuousLinearMapCharacteristicDeterminant (A a i) z ≠ 0 := by
  have h :=
    finiteDimensional_characteristicDeterminant_eventually_abs_gt_half_margin
      A A0 R hR hA0 hA K hKcompact margin hmargin hlimitMargin
  filter_upwards [h] with a ha
  intro i hi z hz
  exact abs_pos.mp (lt_trans (half_pos hmargin) (ha i hi z hz))

end MathlibAnalytic
end MGAP4D
