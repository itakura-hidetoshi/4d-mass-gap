import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAbsoluteCrossCancellationV5_PZ37ABK
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABL — quantitative genuine full/local overlap event

Keep ABH's original signed density C_p=t*Delta_full*Delta_local,p,
ABK's A_p=integral |C_p|, the unchanged full G=integral Delta_full^2,
and the COMPLETE original outer pair-Haar. No physical input changes.

First prove new UNCONDITIONAL density-level bounds, stronger than
bounds on the square of an already integrated correlation:
  J_p := integral C_p^2 <= G*(E_b/2)^2,
  sum_p J_p <= 6*E_b^2*G.
The second uses ABJ's actual all-plaquette pointwise Bessel budget.

An elementary compact-probability threshold estimate is proved using
Young's quadratic inequality and the exact measurable indicator.
It CONSTRUCTS the original open event
  U_p = {z | A_p/2 < |C_p(z)|}
and, whenever A_p>0, proves the positive REAL pair-Haar bound
  (A_p/2)^2 / (G*(E_b/2)^2) <= pairHaar.real U_p.
Both actual full and local GI responses are nonzero on U_p.
ABE and ABK supply an actual link/plaquette with A_p>0 at EVERY
finite H,b>0, so this is an unconditional finite-volume quantitative
simultaneous-response witness, not an assumed local event.

The mass floor equals A_p^2/(E_b^2*G); its H-uniform positive
lower bound is NOT proved. Neither is an H-uniform A_p amplitude,
fixed-support cylinder, full-Hilbert coercivity, common fine interval,
E/F, H1-H4, or continuum Yang-Mills mass gap. In particular, finite-H
positivity is not exchanged with an infimum over H. Original Wilson
kernel, Perron vacuum, Gauss-law sources, actual t>0, TWO interacting
posteriors and all remote pair-Haar coordinates remain unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABL_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABL_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABL_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABL_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABL_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Explicit threshold-mass estimate on the actual probability carrier.
No independent event-mass hypothesis or indicator-continuity assumption.
The proof uses pointwise Young, Bochner monotonicity, and the exact
indicator integral; the event itself is the continuous superlevel set. -/
theorem p4Q2PZ37ABL_compactProbability_threshold_mass_lower
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : C(X, ℝ))
    (m q a : ℝ) (hm : (∫ x, f x ∂μ) = m)
    (hq : 0 < q) (ha : 0 ≤ a) (ham : a < m)
    (hSecond : (∫ x, (f x)^2 ∂μ) ≤ q) :
    (m - a)^2 / q ≤ μ.real {x | a < f x} := by
  let U : Set X := {x | a < f x}
  let d : ℝ := m - a
  let c : ℝ := d^2 / q
  have hd : 0 < d := sub_pos.mpr ham
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) hq.le
  have hcq : c * q = d^2 := div_mul_cancel₀ _ hq.ne'
  have hU : MeasurableSet U :=
    (isOpen_Ioi.preimage f.continuous).measurableSet
  have hf : Integrable (fun x : X => f x) μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfSq : Integrable (fun x : X => (f x)^2) μ :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInd : Integrable (fun x : X => U.indicator (fun _ : X => q) x) μ :=
    (integrable_const q).indicator hU
  have hYoung (x : X) : 2 * d * f x ≤ c * (f x)^2 + q := by
    apply (mul_le_mul_iff_right₀ hq).mp
    calc
      (2 * d * f x) * q ≤ d^2 * (f x)^2 + q^2 := by
        nlinarith only [sq_nonneg (d * f x - q)]
      _ = (c * q) * (f x)^2 + q^2 := by rw [hcq]
      _ = (c * (f x)^2 + q) * q := by ring
  have hPoint (x : X) :
      2 * d * f x ≤ 2 * d * a + c * (f x)^2 +
        U.indicator (fun _ : X => q) x := by
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]
      have hda : 0 ≤ 2 * d * a := by positivity
      linarith [hYoung x]
    · have hxle : f x ≤ a := le_of_not_gt hx
      have hZero : U.indicator (fun _ : X => q) x = 0 := by simp [hx]
      rw [hZero]
      have hScaled : 2 * d * f x ≤ 2 * d * a :=
        mul_le_mul_of_nonneg_left hxle (by positivity)
      have hNonneg : 0 ≤ c * (f x)^2 := mul_nonneg hc (sq_nonneg _)
      linarith
  have hBaseInt : Integrable (fun x : X => 2 * d * a + c * (f x)^2) μ :=
    (integrable_const _).add (hfSq.const_mul c)
  have hI := integral_mono (hf.const_mul (2 * d)) (hBaseInt.add hInd) hPoint
  have hIndicator : (∫ x, U.indicator (fun _ : X => q) x ∂μ) = μ.real U * q := by
    simpa only [smul_eq_mul] using (integral_indicator_const q hU (μ := μ))
  have hLeft : (∫ x, 2 * d * f x ∂μ) = 2 * d * m := by
    rw [integral_const_mul, hm]
  have hConst : (∫ _x : X, 2 * d * a ∂μ) = 2 * d * a := by simp
  have hRight :
      (∫ x, 2 * d * a + c * (f x)^2 + U.indicator (fun _ : X => q) x ∂μ) =
        2 * d * a + c * (∫ x, (f x)^2 ∂μ) + μ.real U * q := by
    rw [integral_add hBaseInt hInd,
      integral_add (integrable_const _) (hfSq.const_mul c),
      hConst, integral_const_mul, hIndicator]
  rw [hLeft, hRight] at hI
  have hCap : c * (∫ x, (f x)^2 ∂μ) ≤ d^2 := by
    calc
      _ ≤ c * q := mul_le_mul_of_nonneg_left hSecond hc
      _ = d^2 := hcq
  have hFinal : d^2 ≤ μ.real U * q := by
    dsimp [d] at hI hCap ⊢
    nlinarith only [hI, hCap]
  exact (div_le_iff₀ hq).2 hFinal

/-- Actual original cross-density SECOND moment, with the square
INSIDE the complete pair-Haar integral, not the squared mean. -/
noncomputable def p4Q2PZ37ABL_originalCrossDensitySecondMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ :=
  ∫ z, (p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z)^2
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- Pointwise genuine mixed response-square envelope. Only the already
proved original local physical GI envelope is used. -/
theorem p4Q2PZ37ABL_originalCrossDensity_sq_le_fullGapSq_scaleSq
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z)^2 ≤
      (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z)^2 *
      (p4Q2LW_originalHarnackContrastScale b / 2)^2 := by
  have hLocal := p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGI_abs_le H b hb e p z
  have hLocalSq := pow_le_pow_left₀ (abs_nonneg _) hLocal 2
  simp only [sq_abs] at hLocalSq
  have hScaled := mul_le_mul_of_nonneg_left hLocalSq
    (sq_nonneg (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z))
  convert hScaled using 1 <;>
    dsimp [p4Q2PZ37ABH_originalCompensatedSignedCrossDensity] <;> ring

/-- Unconditional complete original pair-Haar density moment bound.
It does not assume a common fourth moment or an event mass. -/
theorem p4Q2PZ37ABL_originalCrossDensitySecondMoment_le_fullGI_scaleSq
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2PZ37ABL_originalCrossDensitySecondMoment H b hb e p ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
        (p4Q2LW_originalHarnackContrastScale b / 2)^2 := by
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let F : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let C : Pair → ℝ := p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p
  let s : ℝ := (p4Q2LW_originalHarnackContrastScale b / 2)^2
  have hF : Continuous F := p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
    H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e
  have hC : Continuous C := p4Q2PZ37ABH_originalSignedCrossDensity_continuous H b hb e p
  have hFInt : Integrable (fun z : Pair => (F z)^2) μ :=
    (hF.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCInt : Integrable (fun z : Pair => (C z)^2) μ :=
    (hC.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ z, (C z)^2 ∂μ) ≤ (∫ z, (F z)^2 ∂μ) * s
  calc
    _ ≤ ∫ z, (F z)^2 * s ∂μ := integral_mono hCInt (hFInt.mul_const s)
      (fun z => p4Q2PZ37ABL_originalCrossDensity_sq_le_fullGapSq_scaleSq H b hb e p z)
    _ = (∫ z, (F z)^2 ∂μ) * s := integral_mul_const _ _

/-- The ENTIRE original family of cross-density second moments has
no growing plaquette-count coefficient. The actual full G remains. -/
theorem p4Q2PZ37ABL_originalAllPlaquette_crossDensitySecondMoment_sum_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      p4Q2PZ37ABL_originalCrossDensitySecondMoment H b hb e p) ≤
      6 * (p4Q2LW_originalHarnackContrastScale b)^2 *
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let F : Pair → ℝ := fun z =>
    p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z
  let L (p : Plaq) (z : Pair) : ℝ :=
    p4Q2LW_originalPhysicalTransferNorm H b hb.le *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z
  let C (p : Plaq) : Pair → ℝ :=
    p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p
  let s : ℝ := 6 * (p4Q2LW_originalHarnackContrastScale b)^2
  have hC (p : Plaq) : Continuous (fun z : Pair => (C p z)^2) :=
    (p4Q2PZ37ABH_originalSignedCrossDensity_continuous H b hb e p).pow 2
  have hCInt (p : Plaq) : Integrable (fun z : Pair => (C p z)^2) μ :=
    (hC p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTotalInt : Integrable (fun z : Pair => ∑ p : Plaq, (C p z)^2) μ :=
    (continuous_finset_sum Finset.univ (fun p _hp => hC p)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFInt : Integrable (fun z : Pair => (F z)^2) μ :=
    ((p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e).pow 2)
      .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Pair) : (∑ p : Plaq, (C p z)^2) ≤ (F z)^2 * s := by
    have hEq : (∑ p : Plaq, (C p z)^2) = (F z)^2 * ∑ p : Plaq, (L p z)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      dsimp [C, F, L, p4Q2PZ37ABH_originalCompensatedSignedCrossDensity]
      ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_left
      (p4Q2PZ37ABJ_originalAllPlaquette_pointwise_sq_sum_le H b hb e z) (sq_nonneg _)
  change (∑ p : Plaq, ∫ z, (C p z)^2 ∂μ) ≤ s * ∫ z, (F z)^2 ∂μ
  calc
    _ = ∫ z, ∑ p : Plaq, (C p z)^2 ∂μ := by
      rw [integral_finset_sum (Finset.univ : Finset Plaq) (fun p _hp => hCInt p)]
    _ ≤ ∫ z, (F z)^2 * s ∂μ := integral_mono hTotalInt (hFInt.mul_const s) hPoint
    _ = s * ∫ z, (F z)^2 ∂μ := by rw [integral_mul_const]; ring

/-- Strictly positive ORIGINAL absolute overlap at an actual link and
physical plaquette in every finite volume, obtained from ABE without
assuming any event or changing either interacting Wilson posterior. -/
theorem p4Q2PZ37ABL_exists_originalPositiveAbsoluteCross
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      0 < p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p := by
  obtain ⟨e, p, hK⟩ := p4Q2PZ37ABE_exists_originalLink_plaquette_positiveGlobalGICross H b hb
  refine ⟨e, p, ?_⟩
  have hPos := mul_pos (p4Q2LW_originalPhysicalTransferNorm_pos H b hb.le) hK
  have hN : 0 ≤ p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p := by
    unfold p4Q2PZ37ABJ_originalFullNegativeCrossTail
    exact integral_nonneg (fun _ => le_max_right _ _)
  rw [p4Q2PZ37ABK_originalAbsoluteCross_eq_signed_add_twiceNegative H b hb e p]
  linarith

/-- A genuine original full/local simultaneous-response event, defined
by half the ACTUAL absolute-overlap mean, not by a chosen Haar atom. -/
noncomputable def p4Q2PZ37ABL_originalHalfMeanOverlapEvent
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Set (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :=
  {z | p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p / 2 <
    |p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z|}

/-- Actual quantitative original pair-Haar event construction. Its
positive mass floor equals A^2/(E_b^2*G), but may depend on H. Both
ORIGINAL physical responses are nonzero on this same open event. -/
theorem p4Q2PZ37ABL_originalHalfMeanOverlapEvent_quantitative
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hA : 0 < p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p) :
    IsOpen (p4Q2PZ37ABL_originalHalfMeanOverlapEvent H b hb e p) ∧
    0 < (p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p / 2)^2 /
      (p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
        (p4Q2LW_originalHarnackContrastScale b / 2)^2) ∧
    (p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p / 2)^2 /
      (p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
        (p4Q2LW_originalHarnackContrastScale b / 2)^2) ≤
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).real
        (p4Q2PZ37ABL_originalHalfMeanOverlapEvent H b hb e p) ∧
    ∀ z ∈ p4Q2PZ37ABL_originalHalfMeanOverlapEvent H b hb e p,
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z ≠ 0 ∧
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z ≠ 0 := by
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let A : ℝ := p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e
  let s : ℝ := (p4Q2LW_originalHarnackContrastScale b / 2)^2
  let C : Pair → ℝ := p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p
  let f : C(Pair, ℝ) :=
    ⟨fun z => |C z|, (p4Q2PZ37ABH_originalSignedCrossDensity_continuous H b hb e p).abs⟩
  have hs : 0 < s := pow_pos
    (half_pos (p4Q2LW_originalHarnackContrastScale_pos b hb)) 2
  have hg : 0 < g := lt_of_lt_of_le (div_pos (pow_pos hA 2) hs)
    (p4Q2PZ37ABK_originalFullGIMoment_ge_absoluteCrossSq_div_scaleSq H b hb e p)
  have hq : 0 < g * s := mul_pos hg hs
  have hm : (∫ z, f z ∂μ) = A := rfl
  have hSecond : (∫ z, (f z)^2 ∂μ) ≤ g * s := by
    change (∫ z, |C z|^2 ∂μ) ≤ g * s
    simp only [sq_abs]
    exact p4Q2PZ37ABL_originalCrossDensitySecondMoment_le_fullGI_scaleSq H b hb e p
  have hHalf : A / 2 < A := by change A / 2 < A; linarith
  have hBound := p4Q2PZ37ABL_compactProbability_threshold_mass_lower
    μ f A (g * s) (A / 2) hm hq (half_pos hA).le hHalf hSecond
  have hSub : A - A / 2 = A / 2 := by ring
  rw [hSub] at hBound
  have hOpen : IsOpen (p4Q2PZ37ABL_originalHalfMeanOverlapEvent H b hb e p) :=
    isOpen_Ioi.preimage f.continuous
  refine ⟨hOpen, div_pos (pow_pos (half_pos hA) 2) hq, hBound, ?_⟩
  intro z hz
  have hCne : C z ≠ 0 := abs_pos.mp (lt_trans (half_pos hA) hz)
  constructor
  · intro hZero
    apply hCne
    dsimp [C, p4Q2PZ37ABH_originalCompensatedSignedCrossDensity]
    rw [hZero, zero_mul, mul_zero]
  · intro hZero
    apply hCne
    dsimp [C, p4Q2PZ37ABH_originalCompensatedSignedCrossDensity]
    rw [hZero, mul_zero, mul_zero]

/-- No event existence premise: EVERY finite genuine Wilson volume at
b>0 has an actual link/plaquette with an open simultaneous nonzero GI
event of strictly positive original REAL pair-Haar measure. The preceding
theorem supplies its explicit A^2/(E_b^2*G) mass certificate. -/
theorem p4Q2PZ37ABL_exists_originalPositiveMass_simultaneousGIEvent
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      0 < p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p ∧
      IsOpen (p4Q2PZ37ABL_originalHalfMeanOverlapEvent H b hb e p) ∧
      0 < (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).real
        (p4Q2PZ37ABL_originalHalfMeanOverlapEvent H b hb e p) ∧
      ∀ z ∈ p4Q2PZ37ABL_originalHalfMeanOverlapEvent H b hb e p,
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z ≠ 0 ∧
        p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z ≠ 0 := by
  obtain ⟨e, p, hA⟩ := p4Q2PZ37ABL_exists_originalPositiveAbsoluteCross H b hb
  obtain ⟨hOpen, hPos, hMass, hBoth⟩ :=
    p4Q2PZ37ABL_originalHalfMeanOverlapEvent_quantitative H b hb e p hA
  exact ⟨e, p, hA, hOpen, lt_of_lt_of_le hPos hMass, hBoth⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABL_compactProbability_threshold_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABL_originalCrossDensity_sq_le_fullGapSq_scaleSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABL_originalCrossDensitySecondMoment_le_fullGI_scaleSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABL_originalAllPlaquette_crossDensitySecondMoment_sum_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABL_exists_originalPositiveAbsoluteCross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABL_originalHalfMeanOverlapEvent_quantitative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABL_exists_originalPositiveMass_simultaneousGIEvent
