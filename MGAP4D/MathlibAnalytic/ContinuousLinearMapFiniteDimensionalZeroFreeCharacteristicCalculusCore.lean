import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalCharacteristicDeterminantCore
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- A globally continuous regularization of the scalar reciprocal.  On the
region `cutoff ≤ |x|` it agrees exactly with `x⁻¹`. -/
def regularizedReciprocal (cutoff x : ℝ) : ℝ :=
  x / (max |x| cutoff) ^ 2

/-- A globally continuous regularization of the logarithmic modulus.  On the
region `cutoff ≤ |x|` it agrees exactly with `log |x|`. -/
def regularizedLogAbs (cutoff x : ℝ) : ℝ :=
  Real.log (max |x| cutoff)

/-- Positive cutoff makes the regularized reciprocal continuous everywhere. -/
theorem continuous_regularizedReciprocal (cutoff : ℝ) (hcutoff : 0 < cutoff) :
    Continuous (regularizedReciprocal cutoff) := by
  unfold regularizedReciprocal
  apply Continuous.div continuous_id
    (((continuous_abs.max continuous_const).pow 2))
  intro x
  have hpos : 0 < max |x| cutoff :=
    lt_of_lt_of_le hcutoff (le_max_right _ _)
  exact pow_ne_zero 2 (ne_of_gt hpos)

/-- Positive cutoff makes the regularized logarithmic modulus continuous
everywhere. -/
theorem continuous_regularizedLogAbs (cutoff : ℝ) (hcutoff : 0 < cutoff) :
    Continuous (regularizedLogAbs cutoff) := by
  unfold regularizedLogAbs
  apply Continuous.log (continuous_abs.max continuous_const)
  intro x
  exact ne_of_gt (lt_of_lt_of_le hcutoff (le_max_right _ _))

/-- The reciprocal regularization agrees with the true reciprocal outside the
cutoff interval. -/
theorem regularizedReciprocal_eq_inv
    {cutoff x : ℝ} (hcutoff : cutoff ≤ |x|) (hx : x ≠ 0) :
    regularizedReciprocal cutoff x = x⁻¹ := by
  unfold regularizedReciprocal
  rw [max_eq_left hcutoff, sq_abs]
  field_simp

/-- The logarithmic regularization agrees with the true logarithmic modulus
outside the cutoff interval. -/
theorem regularizedLogAbs_eq_log_abs
    {cutoff x : ℝ} (hcutoff : cutoff ≤ |x|) :
    regularizedLogAbs cutoff x = Real.log |x| := by
  simp [regularizedLogAbs, max_eq_left hcutoff]

/-- The reciprocal characteristic determinant profile. -/
def continuousLinearMapCharacteristicDeterminantReciprocal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  (continuousLinearMapCharacteristicDeterminant A z)⁻¹

/-- The logarithmic absolute characteristic determinant profile. -/
def continuousLinearMapCharacteristicDeterminantLogAbs
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  Real.log |continuousLinearMapCharacteristicDeterminant A z|

/-- A two-point characteristic determinant ratio. -/
def continuousLinearMapCharacteristicDeterminantRatio
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) (z w : ℝ) : ℝ :=
  continuousLinearMapCharacteristicDeterminant A z /
    continuousLinearMapCharacteristicDeterminant A w

/-- Globally continuous regularized reciprocal characteristic profile. -/
def continuousLinearMapCharacteristicDeterminantRegularizedReciprocal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (cutoff : ℝ) (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  regularizedReciprocal cutoff
    (continuousLinearMapCharacteristicDeterminant A z)

/-- Globally continuous regularized logarithmic characteristic profile. -/
def continuousLinearMapCharacteristicDeterminantRegularizedLogAbs
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (cutoff : ℝ) (A : V →L[ℝ] V) (z : ℝ) : ℝ :=
  regularizedLogAbs cutoff
    (continuousLinearMapCharacteristicDeterminant A z)

/-- Globally continuous regularized two-point characteristic ratio. -/
def continuousLinearMapCharacteristicDeterminantRegularizedRatio
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (cutoff : ℝ) (A : V →L[ℝ] V) (p : ℝ × ℝ) : ℝ :=
  continuousLinearMapCharacteristicDeterminant A p.1 *
    regularizedReciprocal cutoff
      (continuousLinearMapCharacteristicDeterminant A p.2)

/-- Joint continuity of the regularized reciprocal characteristic profile. -/
theorem continuous_continuousLinearMapCharacteristicDeterminantRegularizedReciprocal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (cutoff : ℝ) (hcutoff : 0 < cutoff) :
    Continuous (fun p : (V →L[ℝ] V) × ℝ =>
      continuousLinearMapCharacteristicDeterminantRegularizedReciprocal
        cutoff p.1 p.2) := by
  exact (continuous_regularizedReciprocal cutoff hcutoff).comp
    continuous_continuousLinearMapCharacteristicDeterminant

/-- Joint continuity of the regularized logarithmic characteristic profile. -/
theorem continuous_continuousLinearMapCharacteristicDeterminantRegularizedLogAbs
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (cutoff : ℝ) (hcutoff : 0 < cutoff) :
    Continuous (fun p : (V →L[ℝ] V) × ℝ =>
      continuousLinearMapCharacteristicDeterminantRegularizedLogAbs
        cutoff p.1 p.2) := by
  exact (continuous_regularizedLogAbs cutoff hcutoff).comp
    continuous_continuousLinearMapCharacteristicDeterminant

/-- Joint continuity of the regularized two-point characteristic ratio. -/
theorem continuous_continuousLinearMapCharacteristicDeterminantRegularizedRatio
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (cutoff : ℝ) (hcutoff : 0 < cutoff) :
    Continuous (fun p : (V →L[ℝ] V) × (ℝ × ℝ) =>
      continuousLinearMapCharacteristicDeterminantRegularizedRatio
        cutoff p.1 p.2) := by
  let hz : Continuous (fun p : (V →L[ℝ] V) × (ℝ × ℝ) =>
      continuousLinearMapCharacteristicDeterminant p.1 p.2.1) :=
    continuous_continuousLinearMapCharacteristicDeterminant.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  let hw : Continuous (fun p : (V →L[ℝ] V) × (ℝ × ℝ) =>
      continuousLinearMapCharacteristicDeterminant p.1 p.2.2) :=
    continuous_continuousLinearMapCharacteristicDeterminant.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact hz.mul ((continuous_regularizedReciprocal cutoff hcutoff).comp hw)

/-- Uniform convergence in a finite-dimensional normed space passes through a
jointly continuous observable uniformly over an arbitrary additional compact
metric parameter set. -/
theorem finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactParameter
    {α ι P X Y : Type*}
    [PseudoMetricSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {l : Filter α} {s : Set ι}
    (A : α → ι → X) (A0 : ι → X)
    (Phi : X → P → Y)
    (hPhi : Continuous (fun p : X × P => Phi p.1 p.2))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (K : Set P) (hKcompact : IsCompact K) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ p ∈ K,
        ‖Phi (A a i) p - Phi (A0 i) p‖ < epsilon := by
  intro epsilon hepsilon
  let C : Set X := Metric.closedBall 0 (R + 1)
  let D : Set (X × P) := C ×ˢ K
  have hCcompact : IsCompact C := isCompact_closedBall 0 (R + 1)
  have hDcompact : IsCompact D := hCcompact.prod hKcompact
  have hUniform : UniformContinuousOn (fun p : X × P => Phi p.1 p.2) D :=
    hDcompact.uniformContinuousOn_of_continuous hPhi.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp hUniform) epsilon hepsilon with
    ⟨delta, hdelta, hmodulus⟩
  let eta : ℝ := min delta 1
  have heta : 0 < eta := lt_min hdelta zero_lt_one
  have hApprox := hA eta heta
  filter_upwards [hApprox] with a ha
  intro i hi p hp
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
  have hpair0 : (A0 i, p) ∈ D := ⟨hA0C, hp⟩
  have hpair : (A a i, p) ∈ D := ⟨hAC, hp⟩
  have hdist : dist (A a i, p) (A0 i, p) < delta := by
    simpa [Prod.dist_eq, dist_eq_norm] using hdiffDelta
  have hout := hmodulus (A a i, p) hpair (A0 i, p) hpair0 hdist
  simpa [dist_eq_norm] using hout

/-- Uniform finite-dimensional operator convergence and a positive continuum
characteristic margin imply compact-uniform convergence of reciprocal
characteristic profiles. -/
theorem finiteDimensional_characteristicDeterminantReciprocal_tendsto_uniformOn_compactRealParameter
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal (A a i) z -
          continuousLinearMapCharacteristicDeterminantReciprocal (A0 i) z| < epsilon := by
  intro epsilon hepsilon
  let cutoff : ℝ := margin / 4
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; linarith
  have hzero :=
    finiteDimensional_characteristicDeterminant_eventually_abs_gt_half_margin
      A A0 R hR hA0 hA Z hZcompact margin hmargin hlimitMargin
  have hreg :=
    finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactParameter
      A A0
      (continuousLinearMapCharacteristicDeterminantRegularizedReciprocal cutoff)
      (continuous_continuousLinearMapCharacteristicDeterminantRegularizedReciprocal
        cutoff hcutoff)
      R hR hA0 hA Z hZcompact epsilon hepsilon
  filter_upwards [hzero, hreg] with a hazero hareg
  intro i hi z hz
  let x := continuousLinearMapCharacteristicDeterminant (A a i) z
  let y := continuousLinearMapCharacteristicDeterminant (A0 i) z
  have hxhalf : margin / 2 < |x| := hazero i hi z hz
  have hy : margin ≤ |y| := hlimitMargin i hi z hz
  have hxne : x ≠ 0 := abs_pos.mp (lt_trans (by linarith) hxhalf)
  have hyne : y ≠ 0 := abs_pos.mp (lt_of_lt_of_le hmargin hy)
  have hcutx : cutoff ≤ |x| := by dsimp [cutoff]; linarith
  have hcuty : cutoff ≤ |y| := by dsimp [cutoff]; linarith
  simpa [continuousLinearMapCharacteristicDeterminantReciprocal,
    continuousLinearMapCharacteristicDeterminantRegularizedReciprocal,
    regularizedReciprocal_eq_inv hcutx hxne,
    regularizedReciprocal_eq_inv hcuty hyne,
    Real.norm_eq_abs, x, y] using hareg i hi z hz

/-- Under the same positive margin, logarithmic absolute characteristic
profiles converge compact-uniformly. -/
theorem finiteDimensional_characteristicDeterminantLogAbs_tendsto_uniformOn_compactRealParameter
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs (A a i) z -
          continuousLinearMapCharacteristicDeterminantLogAbs (A0 i) z| < epsilon := by
  intro epsilon hepsilon
  let cutoff : ℝ := margin / 4
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; linarith
  have hzero :=
    finiteDimensional_characteristicDeterminant_eventually_abs_gt_half_margin
      A A0 R hR hA0 hA Z hZcompact margin hmargin hlimitMargin
  have hreg :=
    finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactParameter
      A A0
      (continuousLinearMapCharacteristicDeterminantRegularizedLogAbs cutoff)
      (continuous_continuousLinearMapCharacteristicDeterminantRegularizedLogAbs
        cutoff hcutoff)
      R hR hA0 hA Z hZcompact epsilon hepsilon
  filter_upwards [hzero, hreg] with a hazero hareg
  intro i hi z hz
  let x := continuousLinearMapCharacteristicDeterminant (A a i) z
  let y := continuousLinearMapCharacteristicDeterminant (A0 i) z
  have hxhalf : margin / 2 < |x| := hazero i hi z hz
  have hy : margin ≤ |y| := hlimitMargin i hi z hz
  have hcutx : cutoff ≤ |x| := by dsimp [cutoff]; linarith
  have hcuty : cutoff ≤ |y| := by dsimp [cutoff]; linarith
  simpa [continuousLinearMapCharacteristicDeterminantLogAbs,
    continuousLinearMapCharacteristicDeterminantRegularizedLogAbs,
    regularizedLogAbs_eq_log_abs hcutx,
    regularizedLogAbs_eq_log_abs hcuty,
    Real.norm_eq_abs, x, y] using hareg i hi z hz

/-- A positive denominator margin implies compact-uniform convergence of
characteristic determinant ratios on two compact real parameter sets. -/
theorem finiteDimensional_characteristicDeterminantRatio_tendsto_uniformOn_compactRealParameter_product
    {α ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter α} {s : Set ι}
    (A : α → ι → (V →L[ℝ] V)) (A0 : ι → (V →L[ℝ] V))
    (R : ℝ) (hR : 0 ≤ R)
    (hA0 : ∀ i ∈ s, ‖A0 i‖ ≤ R)
    (hA : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ i ∈ s, ‖A a i - A0 i‖ < eta)
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ i ∈ s, ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (A0 i) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ i ∈ s, ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio (A a i) z w -
          continuousLinearMapCharacteristicDeterminantRatio (A0 i) z w| < epsilon := by
  intro epsilon hepsilon
  let cutoff : ℝ := margin / 4
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; linarith
  have hzero :=
    finiteDimensional_characteristicDeterminant_eventually_abs_gt_half_margin
      A A0 R hR hA0 hA W hWcompact margin hmargin hlimitMargin
  have hreg :=
    finiteDimensional_jointContinuousObservable_tendsto_uniformOn_compactParameter
      A A0
      (continuousLinearMapCharacteristicDeterminantRegularizedRatio cutoff)
      (continuous_continuousLinearMapCharacteristicDeterminantRegularizedRatio
        cutoff hcutoff)
      R hR hA0 hA (Z ×ˢ W) (hZcompact.prod hWcompact) epsilon hepsilon
  filter_upwards [hzero, hreg] with a hazero hareg
  intro i hi z hz w hw
  let xa := continuousLinearMapCharacteristicDeterminant (A a i) w
  let x0 := continuousLinearMapCharacteristicDeterminant (A0 i) w
  have xahalf : margin / 2 < |xa| := hazero i hi w hw
  have hx0 : margin ≤ |x0| := hlimitMargin i hi w hw
  have hxane : xa ≠ 0 := abs_pos.mp (lt_trans (by linarith) xahalf)
  have hx0ne : x0 ≠ 0 := abs_pos.mp (lt_of_lt_of_le hmargin hx0)
  have hcutxa : cutoff ≤ |xa| := by dsimp [cutoff]; linarith
  have hcutx0 : cutoff ≤ |x0| := by dsimp [cutoff]; linarith
  have h := hareg i hi (z, w) ⟨hz, hw⟩
  simpa [continuousLinearMapCharacteristicDeterminantRatio,
    continuousLinearMapCharacteristicDeterminantRegularizedRatio,
    regularizedReciprocal_eq_inv hcutxa hxane,
    regularizedReciprocal_eq_inv hcutx0 hx0ne,
    div_eq_mul_inv, Real.norm_eq_abs, xa, x0] using h

end MathlibAnalytic
end MGAP4D
