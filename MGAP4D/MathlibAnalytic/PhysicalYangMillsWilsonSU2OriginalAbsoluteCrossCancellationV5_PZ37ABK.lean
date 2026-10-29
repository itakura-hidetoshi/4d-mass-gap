import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPlaquetteResponseBesselBudgetV5_PZ37ABJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABK — original absolute cross and exact cancellation defect

Retain the SAME genuine Wilson signed density C_p=t*Delta_full*Delta_local,p,
actual transfer t>0, Gauss-law physical sources, Perron vacuum, TWO
interacting posteriors, and COMPLETE original outer pair-Haar.
Define A_p=integral |C_p|, not |integral C_p|. With c_p=t*K_p and
ABJ's entire negative part N_p, prove exactly A_p=c_p+2*N_p.

Absolute-product Cauchy gives A_p^2<=G*Mcomp_p. Thus ABJ improves to
  sum_p A_p^2 <= 6*E_b^2*G,
  4*N_p*(N_p+c_p) <= G*Mcomp_p-c_p^2.
When c_p>=0, N_p^2 <= (G*Mcomp_p-c_p^2)/4. The original signed
correlation is retained rather than discarded in the negative-tail bound.

A separate sufficient route to the SAME unweighted full GI moment is
  A_p^2/(E_b/2)^2 <= G.
For 0<b(H)<=B, a common A_p>=alpha>0 yields G>=4*alpha^2/E_B^2
WITHOUT a common positive SIGNED c_p or an independent negative-tail cap.
This is a new conditional implication, not a proof of the needed uniform
absolute-overlap witness, nor of the old uniform signed-kappa statement.

All unconditional estimates are on the actual original Wilson model.
No posterior independence substitution, t=1, source replacement, extra
axioms, native_decide, Dobrushin, common fine interval, all-Hilbert
coercivity, E/F, H1-H4 or continuum Yang-Mills mass-gap closure.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABK_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABK_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABK_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABK_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABK_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Absolute-product Cauchy on the unchanged compact probability carrier.
The absolute value is INSIDE the integral, so signed cancellation does
not reduce the left-hand side. -/
theorem p4Q2PZ37ABK_compactProbability_absoluteCrossIntegral_sq_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : C(X, ℝ)) :
    (∫ x, |f x * g x| ∂μ)^2 ≤
      (∫ x, (f x)^2 ∂μ) * (∫ x, (g x)^2 ∂μ) := by
  let F : C(X, ℝ) := ⟨fun x => |f x|, f.continuous.abs⟩
  let L : C(X, ℝ) := ⟨fun x => |g x|, g.continuous.abs⟩
  have hCS := p4Q2PZ37ABG_compactProbability_integral_cross_sq_le μ F L
  change (∫ x, |f x| * |g x| ∂μ)^2 ≤
    (∫ x, |f x|^2 ∂μ) * (∫ x, |g x|^2 ∂μ) at hCS
  simpa only [abs_mul, sq_abs] using hCS

/-- Absolute overlap of the SAME genuine full/local physical GI responses,
integrated against ALL original boundary pair-Haar coordinates. This is
not a new physical source or conditional posterior. -/
noncomputable def p4Q2PZ37ABK_originalAbsoluteCrossMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ :=
  ∫ z, |p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z|
    ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2

/-- Exact original total-variation identity A=c+2N, with the ENTIRE
negative original pair-Haar contribution retained. Valid for both signs
of c and when any of these original responses vanish. -/
theorem p4Q2PZ37ABK_originalAbsoluteCross_eq_signed_add_twiceNegative
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p =
      p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p +
      2 * p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p := by
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let C : Pair → ℝ := p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p
  have hCont : Continuous C :=
    p4Q2PZ37ABH_originalSignedCrossDensity_continuous H b hb e p
  have hCInt : Integrable C μ :=
    hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNegInt : Integrable (fun z : Pair => max (-C z) 0) μ :=
    (hCont.neg.max continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Pair) : |C z| = C z + 2 * max (-C z) 0 := by
    by_cases hz : 0 ≤ C z
    · rw [abs_of_nonneg hz, max_eq_right (neg_nonpos.mpr hz)]
      ring
    · have hz' : C z ≤ 0 := le_of_lt (lt_of_not_ge hz)
      rw [abs_of_nonpos hz', max_eq_left (neg_nonneg.mpr hz')]
      ring
  have hMean : (∫ z, C z ∂μ) =
      p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p :=
    p4Q2PZ37ABH_originalSignedCrossDensity_integral_eq_trueCross H b hb e p
  change (∫ z, |C z| ∂μ) = _
  calc
    (∫ z, |C z| ∂μ) = ∫ z, (C z + 2 * max (-C z) 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      exact hPoint z
    _ = (∫ z, C z ∂μ) + 2 * (∫ z, max (-C z) 0 ∂μ) := by
      rw [integral_add hCInt (hNegInt.const_mul 2), integral_const_mul]
    _ = p4Q2LW_originalPhysicalTransferNorm H b hb.le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p +
        2 * p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p :=
      congrArg (fun v : ℝ => v +
        2 * p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p) hMean

/-- Original absolute cross square is bounded by the SAME full G and
actual compensated local moment. No signed-cross positivity premise. -/
theorem p4Q2PZ37ABK_originalAbsoluteCross_sq_le_fullGI_mul_localMoment
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p)^2 ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
        p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e p := by
  let Pair := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let μ : Measure Pair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let t : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le
  let F : C(Pair, ℝ) :=
    ⟨fun z => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e z,
      p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
        H b hb.le (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) e⟩
  let L : C(Pair, ℝ) :=
    ⟨fun z => t * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb.le
      (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e z,
      continuous_const.mul
        (p4Q2HI_originalWilsonTwoPosteriorExpectationGap_continuous
          H b hb.le
          (p4Q2PZ37ABD_originalCenteredLocalPlaquettePhysicalSource H p) e)⟩
  have hProduct (z : Pair) :
      p4Q2PZ37ABH_originalCompensatedSignedCrossDensity H b hb e p z =
        F z * L z := by
    dsimp [p4Q2PZ37ABH_originalCompensatedSignedCrossDensity, F, L, t]
    ring
  have hA : p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p =
      ∫ z, |F z * L z| ∂μ := by
    unfold p4Q2PZ37ABK_originalAbsoluteCrossMoment
    apply integral_congr_ae
    filter_upwards with z
    rw [hProduct z]
  rw [hA]
  exact p4Q2PZ37ABK_compactProbability_absoluteCrossIntegral_sq_le μ F L

/-- ABJ's genuine Bessel estimate controls ALL absolute overlaps, not
only signed integrals. The original full G is retained on the right. -/
theorem p4Q2PZ37ABK_originalAllPlaquette_absoluteCross_sq_sum_le
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      (p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p)^2) ≤
      6 * (p4Q2LW_originalHarnackContrastScale b)^2 *
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e
  let E : ℝ := p4Q2LW_originalHarnackContrastScale b
  let M := p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e
  have hg : 0 ≤ g := by
    dsimp [g]
    unfold p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    exact integral_nonneg (fun _ => sq_nonneg _)
  calc
    (∑ p : Plaq, (p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p)^2) ≤
        ∑ p : Plaq, g * M p := by
      apply Finset.sum_le_sum
      intro p _hp
      exact p4Q2PZ37ABK_originalAbsoluteCross_sq_le_fullGI_mul_localMoment H b hb e p
    _ = g * ∑ p : Plaq, M p := (Finset.mul_sum _ _ _).symm
    _ ≤ g * (6 * E^2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37ABJ_originalAllPlaquette_compensatedMoment_sum_le H b hb e) hg
    _ = 6 * E^2 * g := by ring

/-- Exact quantitative cancellation cost: positive and negative parts
can coexist only within the actual Cauchy defect. Valid even if the
original signed cross is negative. -/
theorem p4Q2PZ37ABK_originalNegativeTail_product_le_cauchyDefect
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    4 * p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p *
      (p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p +
        p4Q2LW_originalPhysicalTransferNorm H b hb.le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p) ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
        p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e p -
      (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2 := by
  have hCS :=
    p4Q2PZ37ABK_originalAbsoluteCross_sq_le_fullGI_mul_localMoment H b hb e p
  rw [p4Q2PZ37ABK_originalAbsoluteCross_eq_signed_add_twiceNegative H b hb e p] at hCS
  nlinarith only [hCS]

/-- At a nonnegative actual signed cross, the negative-tail square is
bounded by ONE QUARTER of the actual Cauchy defect, improving ABJ's
G*M ceiling and retaining the positive-correlation subtraction. -/
theorem p4Q2PZ37ABK_originalNegativeTail_sq_le_quarterDefect_of_nonnegCross
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hK : 0 ≤ p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p) :
    (p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p)^2 ≤
      (p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e *
          p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e p -
        (p4Q2LW_originalPhysicalTransferNorm H b hb.le *
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p)^2) / 4 := by
  let n : ℝ := p4Q2PZ37ABJ_originalFullNegativeCrossTail H b hb e p
  let c : ℝ := p4Q2LW_originalPhysicalTransferNorm H b hb.le *
    p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e
  let m : ℝ := p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment H b hb e p
  have hn : 0 ≤ n := by
    dsimp [n]
    unfold p4Q2PZ37ABJ_originalFullNegativeCrossTail
    exact integral_nonneg (fun _ => le_max_right _ _)
  have hc : 0 ≤ c :=
    mul_nonneg (p4Q2LW_originalPhysicalTransferNorm_pos H b hb.le).le hK
  have hBudget : 4 * n * (n + c) ≤ g * m - c^2 :=
    p4Q2PZ37ABK_originalNegativeTail_product_le_cauchyDefect H b hb e p
  have hnc : 0 ≤ n * c := mul_nonneg hn hc
  change n^2 ≤ (g * m - c^2) / 4
  nlinarith only [hBudget, hnc]

/-- A sign-free lower certificate for the UNCHANGED original full GI
moment. Absolute local overlap suffices; it is not necessary to first
establish a positive signed correlation or suppress its negative tail. -/
theorem p4Q2PZ37ABK_originalFullGIMoment_ge_absoluteCrossSq_div_scaleSq
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    (p4Q2PZ37ABK_originalAbsoluteCrossMoment H b hb e p)^2 /
        (p4Q2LW_originalHarnackContrastScale b / 2)^2 ≤
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
  have hDen : 0 < (p4Q2LW_originalHarnackContrastScale b / 2)^2 :=
    pow_pos (half_pos (p4Q2LW_originalHarnackContrastScale_pos b hb)) 2
  have hg : 0 ≤ p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e := by
    unfold p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    exact integral_nonneg (fun _ => sq_nonneg _)
  apply (div_le_iff₀ hDen).2
  exact (p4Q2PZ37ABK_originalAbsoluteCross_sq_le_fullGI_mul_localMoment H b hb e p).trans
    (mul_le_mul_of_nonneg_left
      (p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment_le_uniform H b hb e p) hg)

/-- A new separate all-volume sufficient route: a uniform ORIGINAL
absolute-overlap witness implies a full GI floor at bounded positive
coupling. No signed-kappa or negative-tail premise is used. Existence of
this uniform absolute witness is NOT established by this theorem. -/
theorem p4Q2PZ37ABK_allVolumes_fullGIfloor_of_absoluteCross_boundedCoupling
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ H, b H ≤ B)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hWitness : ∀ H,
      ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
        alpha ≤ p4Q2PZ37ABK_originalAbsoluteCrossMoment H (b H) (hb H) e p) :
    0 < alpha^2 / (p4Q2LW_originalHarnackContrastScale B / 2)^2 ∧
    ∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      alpha^2 / (p4Q2LW_originalHarnackContrastScale B / 2)^2 ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e := by
  have hDen : 0 < (p4Q2LW_originalHarnackContrastScale B / 2)^2 :=
    pow_pos (half_pos (p4Q2LW_originalHarnackContrastScale_pos B hB)) 2
  refine ⟨div_pos (pow_pos halpha 2) hDen, ?_⟩
  intro H
  obtain ⟨e, p, hA⟩ := hWitness H
  refine ⟨e, ?_⟩
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H (b H) (hb H) e
  let A : ℝ := p4Q2PZ37ABK_originalAbsoluteCrossMoment H (b H) (hb H) e p
  let s : ℝ := p4Q2LW_originalHarnackContrastScale (b H)
  let sB : ℝ := p4Q2LW_originalHarnackContrastScale B
  have hg : 0 ≤ g := by
    dsimp [g]
    unfold p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment
    exact integral_nonneg (fun _ => sq_nonneg _)
  have hs : 0 < s := p4Q2LW_originalHarnackContrastScale_pos (b H) (hb H)
  have hScale : s ≤ sB :=
    p4Q2PZ37ABI_originalHarnackContrastScale_mono (b H) B (hb H).le (hBound H)
  have hHalf : s / 2 ≤ sB / 2 := by linarith
  have hScaleSq : (s / 2)^2 ≤ (sB / 2)^2 :=
    pow_le_pow_left₀ (half_pos hs).le hHalf 2
  have hCS : A^2 ≤ g * (s / 2)^2 :=
    (p4Q2PZ37ABK_originalAbsoluteCross_sq_le_fullGI_mul_localMoment
      H (b H) (hb H) e p).trans
      (mul_le_mul_of_nonneg_left
        (p4Q2PZ37ABF2_originalCompensatedLocalPhysicalGIMoment_le_uniform
          H (b H) (hb H) e p) hg)
  have hAlphaSq : alpha^2 ≤ A^2 := pow_le_pow_left₀ halpha.le hA 2
  apply (div_le_iff₀ hDen).2
  exact hAlphaSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hScaleSq hg))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_compactProbability_absoluteCrossIntegral_sq_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_originalAbsoluteCross_eq_signed_add_twiceNegative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_originalAbsoluteCross_sq_le_fullGI_mul_localMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_originalAllPlaquette_absoluteCross_sq_sum_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_originalNegativeTail_product_le_cauchyDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_originalNegativeTail_sq_le_quarterDefect_of_nonnegCross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_originalFullGIMoment_ge_absoluteCrossSq_div_scaleSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABK_allVolumes_fullGIfloor_of_absoluteCross_boundedCoupling
