import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalResidualWeightedInfluence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# RMS energy transport for the exact one-link overlap coupling

This file upgrades the exact overlap-coupling spine from unmatched mass and
sup-norm estimates to centered mean-square energy.

For a strongly measurable real fiber observable X and any center c, the
diagonal branch of the overlap coupling contributes zero to
  (X(g₁) - X(g₂))².
The residual product branch has exact left/right residual marginals, so
  E[(X(g₁)-X(g₂))²]
is bounded by twice the sum of the centered-square residual energies.

The weighted residual-density theorem from the preceding unit then converts
that residual-energy sum into the sharp likelihood-ratio influence coefficient
times the two full conditional centered-square energies.

This is the RMS replacement for the older bound
  off-diagonal mass × (2 * sup-norm)².
No volume/cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The residual-product branch of the canonical exact one-link overlap
coupling.  It is zero when the unmatched mass vanishes and otherwise is the
normalized product of the two residual measures. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualProductCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure (C.base.Gauge × C.base.Gauge) :=
  let delta := C.singleLinkConditionalResidualMass A B target
  if delta = 0 then
    0
  else
    delta⁻¹ •
      ((C.singleLinkConditionalLeftResidualMeasure A B target).prod
        (C.singleLinkConditionalRightResidualMeasure A B target))

/-- The first marginal of the residual-product branch is exactly the left
residual measure. -/
theorem
    continuous_compact_oriented_map_fst_singleLinkConditionalResidualProductCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.singleLinkConditionalResidualProductCouplingMeasure A B target) =
      C.singleLinkConditionalLeftResidualMeasure A B target := by
  let left := C.singleLinkConditionalLeftResidualMeasure A B target
  let right := C.singleLinkConditionalRightResidualMeasure A B target
  let delta := C.singleLinkConditionalResidualMass A B target
  change
    Measure.map Prod.fst
      (if delta = 0 then 0 else delta⁻¹ • left.prod right) = left
  by_cases hdelta : delta = 0
  · rw [if_pos hdelta]
    have hLeftZero : left = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa [left, delta,
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualMass]
        using hdelta
    simp [hLeftZero]
  · rw [if_neg hdelta, Measure.map_smul, Measure.map_fst_prod]
    rw [show right univ = delta by
      simpa [right, delta] using
        continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ
          C A B target]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hdelta
        (continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
          C A B target),
      one_smul]

/-- The second marginal of the residual-product branch is exactly the right
residual measure. -/
theorem
    continuous_compact_oriented_map_snd_singleLinkConditionalResidualProductCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.singleLinkConditionalResidualProductCouplingMeasure A B target) =
      C.singleLinkConditionalRightResidualMeasure A B target := by
  let left := C.singleLinkConditionalLeftResidualMeasure A B target
  let right := C.singleLinkConditionalRightResidualMeasure A B target
  let delta := C.singleLinkConditionalResidualMass A B target
  change
    Measure.map Prod.snd
      (if delta = 0 then 0 else delta⁻¹ • left.prod right) = right
  by_cases hdelta : delta = 0
  · rw [if_pos hdelta]
    have hRightZero : right = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [show right univ = delta by
        simpa [right, delta] using
          continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ
            C A B target]
      exact hdelta
    simp [hRightZero]
  · rw [if_neg hdelta, Measure.map_smul, Measure.map_snd_prod]
    rw [show left univ = delta by rfl]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hdelta
        (continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
          C A B target),
      one_smul]

/-- The exact overlap coupling splits into its common diagonal branch plus the
named residual-product branch. -/
theorem
    continuous_compact_oriented_singleLinkConditionalOverlapCouplingMeasure_eq_diagonal_add_residualProduct
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalOverlapCouplingMeasure A B target =
      Measure.map (fun g : C.base.Gauge => (g, g))
          (C.singleLinkConditionalOverlapMeasure A B target) +
        C.singleLinkConditionalResidualProductCouplingMeasure A B target := by
  rfl

/-- Pure coupling-energy statement: the mean-square difference under the exact
overlap coupling is at most twice the sum of the centered-square energies of
the two residual marginals.

The center is arbitrary; later it may be chosen as a conditional mean or any
other convenient outer-context center. -/
theorem
    continuous_compact_oriented_singleLinkConditionalOverlapCoupling_centeredSquare_lintegral_le_two_residual
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (X : C.base.Gauge → ℝ)
    (hX : StronglyMeasurable X)
    (center : ℝ) :
    (∫⁻ z,
      ENNReal.ofReal ((X z.1 - X z.2) ^ 2)
      ∂C.singleLinkConditionalOverlapCouplingMeasure A B target) ≤
      (2 : ℝ≥0∞) *
        ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
            ∂C.singleLinkConditionalLeftResidualMeasure A B target) +
          ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
            ∂C.singleLinkConditionalRightResidualMeasure A B target) := by
  let overlap := C.singleLinkConditionalOverlapMeasure A B target
  let residual :=
    C.singleLinkConditionalResidualProductCouplingMeasure A B target
  let W : C.base.Gauge → ℝ≥0∞ :=
    fun g => ENNReal.ofReal ((X g - center) ^ 2)
  let F : C.base.Gauge × C.base.Gauge → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((X z.1 - X z.2) ^ 2)
  have hXm : Measurable X := hX.measurable
  have hW : Measurable W := by
    dsimp [W]
    exact ENNReal.measurable_ofReal.comp
      ((hXm.sub measurable_const).pow_const 2)
  have hF : Measurable F := by
    dsimp [F]
    exact ENNReal.measurable_ofReal.comp
      (((hXm.comp measurable_fst).sub
        (hXm.comp measurable_snd)).pow_const 2)
  have hDiagMap : Measurable (fun g : C.base.Gauge => (g, g)) :=
    measurable_id.prodMk measurable_id
  have hDiag :
      (∫⁻ z, F z
        ∂Measure.map (fun g : C.base.Gauge => (g, g)) overlap) = 0 := by
    rw [lintegral_map hF hDiagMap]
    simp [F]
  have hCoupling :
      C.singleLinkConditionalOverlapCouplingMeasure A B target =
        Measure.map (fun g : C.base.Gauge => (g, g)) overlap + residual := by
    simpa [overlap, residual] using
      continuous_compact_oriented_singleLinkConditionalOverlapCouplingMeasure_eq_diagonal_add_residualProduct
        C A B target
  have hFull :
      (∫⁻ z, F z
        ∂C.singleLinkConditionalOverlapCouplingMeasure A B target) =
      ∫⁻ z, F z ∂residual := by
    rw [hCoupling, lintegral_add_measure, hDiag, zero_add]
  have hPoint : ∀ z : C.base.Gauge × C.base.Gauge,
      F z ≤ (2 : ℝ≥0∞) * (W z.1 + W z.2) := by
    intro z
    have hReal :
        (X z.1 - X z.2) ^ 2 ≤
          2 * ((X z.1 - center) ^ 2 + (X z.2 - center) ^ 2) := by
      nlinarith [sq_nonneg ((X z.1 - center) + (X z.2 - center))]
    dsimp [F, W]
    calc
      ENNReal.ofReal ((X z.1 - X z.2) ^ 2) ≤
          ENNReal.ofReal
            (2 * ((X z.1 - center) ^ 2 + (X z.2 - center) ^ 2)) :=
        ENNReal.ofReal_le_ofReal hReal
      _ =
          (2 : ℝ≥0∞) *
            (ENNReal.ofReal ((X z.1 - center) ^ 2) +
              ENNReal.ofReal ((X z.2 - center) ^ 2)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
        norm_num
  have hWfst : Measurable (fun z : C.base.Gauge × C.base.Gauge => W z.1) :=
    hW.comp measurable_fst
  have hWsnd : Measurable (fun z : C.base.Gauge × C.base.Gauge => W z.2) :=
    hW.comp measurable_snd
  have hResidualBound :
      (∫⁻ z, F z ∂residual) ≤
        (2 : ℝ≥0∞) *
          ((∫⁻ g, W g
              ∂C.singleLinkConditionalLeftResidualMeasure A B target) +
            ∫⁻ g, W g
              ∂C.singleLinkConditionalRightResidualMeasure A B target) := by
    calc
      (∫⁻ z, F z ∂residual) ≤
          ∫⁻ z, (2 : ℝ≥0∞) * (W z.1 + W z.2) ∂residual :=
        lintegral_mono hPoint
      _ =
          (2 : ℝ≥0∞) *
            ∫⁻ z, (W z.1 + W z.2) ∂residual := by
        rw [lintegral_const_mul'' _ (hWfst.add hWsnd).aemeasurable]
      _ =
          (2 : ℝ≥0∞) *
            ((∫⁻ z, W z.1 ∂residual) +
              ∫⁻ z, W z.2 ∂residual) := by
        rw [lintegral_add_left hWfst]
      _ =
          (2 : ℝ≥0∞) *
            ((∫⁻ g, W g
                ∂C.singleLinkConditionalLeftResidualMeasure A B target) +
              ∫⁻ g, W g
                ∂C.singleLinkConditionalRightResidualMeasure A B target) := by
        rw [← lintegral_map hW measurable_fst,
          continuous_compact_oriented_map_fst_singleLinkConditionalResidualProductCouplingMeasure
            C A B target]
        rw [← lintegral_map hW measurable_snd,
          continuous_compact_oriented_map_snd_singleLinkConditionalResidualProductCouplingMeasure
            C A B target]
  rw [hFull]
  simpa [W] using hResidualBound

/-- The centered-square left/right residual energies are bounded by the same
sharp likelihood-ratio coefficient times the centered-square energies under
the two full conditional laws. -/
theorem
    continuous_compact_oriented_singleLinkConditionalResidualMeasure_centeredSquare_sum_lintegral_le_coefficient
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          K * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          K * C.singleLinkConditionalDensityReal A target g)
    (X : C.base.Gauge → ℝ)
    (hX : StronglyMeasurable X)
    (center : ℝ) :
    ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
        ∂C.singleLinkConditionalLeftResidualMeasure A B target) +
      ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
        ∂C.singleLinkConditionalRightResidualMeasure A B target) ≤
      ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
        ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
            ∂C.singleLinkConditionalMeasure A target) +
          ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
            ∂C.singleLinkConditionalMeasure B target) := by
  let μ := normalizedCompactHaar C.base.Gauge
  let W : C.base.Gauge → ℝ≥0∞ :=
    fun g => ENNReal.ofReal ((X g - center) ^ 2)
  let lD := C.singleLinkConditionalLeftResidualDensity A B target
  let rD := C.singleLinkConditionalRightResidualDensity A B target
  let p := C.singleLinkConditionalDensity target A
  let q := C.singleLinkConditionalDensity target B
  let coeff : ℝ≥0∞ := ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K)
  have hXm : Measurable X := hX.measurable
  have hW : Measurable W := by
    dsimp [W]
    exact ENNReal.measurable_ofReal.comp
      ((hXm.sub measurable_const).pow_const 2)
  have hlD : Measurable lD := by
    simpa [lD] using
      continuous_compact_oriented_singleLinkConditionalLeftResidualDensity_measurable
        C A B target
  have hrD : Measurable rD := by
    simpa [rD] using
      continuous_compact_oriented_singleLinkConditionalRightResidualDensity_measurable
        C A B target
  have hp : Measurable p := by
    simpa [p] using
      continuous_compact_oriented_singleLinkConditionalDensity_measurable
        C A target
  have hq : Measurable q := by
    simpa [q] using
      continuous_compact_oriented_singleLinkConditionalDensity_measurable
        C B target
  have hRaw :=
    continuous_compact_oriented_singleLinkConditionalResidualDensity_weighted_lintegral_le_coefficient
      C A B target K hK hRatio W
  have hLeft :
      (∫⁻ g, W g
        ∂C.singleLinkConditionalLeftResidualMeasure A B target) =
      ∫⁻ g, W g * lD g ∂μ := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualMeasure
    rw [lintegral_withDensity_eq_lintegral_mul μ hlD hW]
    apply lintegral_congr
    intro g
    simp [lD, mul_comm]
  have hRight :
      (∫⁻ g, W g
        ∂C.singleLinkConditionalRightResidualMeasure A B target) =
      ∫⁻ g, W g * rD g ∂μ := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualMeasure
    rw [lintegral_withDensity_eq_lintegral_mul μ hrD hW]
    apply lintegral_congr
    intro g
    simp [rD, mul_comm]
  have hMeasureA :
      C.singleLinkConditionalMeasure A target = μ.withDensity p := by
    simpa [μ, p] using
      continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity
        C A target
  have hMeasureB :
      C.singleLinkConditionalMeasure B target = μ.withDensity q := by
    simpa [μ, q] using
      continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity
        C B target
  have hA :
      (∫⁻ g, W g ∂C.singleLinkConditionalMeasure A target) =
      ∫⁻ g, W g * p g ∂μ := by
    rw [hMeasureA, lintegral_withDensity_eq_lintegral_mul μ hp hW]
    apply lintegral_congr
    intro g
    exact mul_comm (p g) (W g)
  have hB :
      (∫⁻ g, W g ∂C.singleLinkConditionalMeasure B target) =
      ∫⁻ g, W g * q g ∂μ := by
    rw [hMeasureB, lintegral_withDensity_eq_lintegral_mul μ hq hW]
    apply lintegral_congr
    intro g
    exact mul_comm (q g) (W g)
  have hRawLeft :
      (∫⁻ g, W g * (lD g + rD g) ∂μ) =
        (∫⁻ g, W g * lD g ∂μ) +
          ∫⁻ g, W g * rD g ∂μ := by
    calc
      (∫⁻ g, W g * (lD g + rD g) ∂μ) =
          ∫⁻ g, (W g * lD g + W g * rD g) ∂μ := by
        apply lintegral_congr
        intro g
        rw [mul_add]
      _ = _ := by
        rw [lintegral_add_left (hW.mul hlD)]
  have hRawRight :
      (∫⁻ g, W g * (coeff * (p g + q g)) ∂μ) =
        coeff *
          ((∫⁻ g, W g * p g ∂μ) +
            ∫⁻ g, W g * q g ∂μ) := by
    calc
      (∫⁻ g, W g * (coeff * (p g + q g)) ∂μ) =
          ∫⁻ g, coeff * (W g * p g + W g * q g) ∂μ := by
        apply lintegral_congr
        intro g
        simp only [mul_add]
        ac_rfl
      _ = coeff *
          ∫⁻ g, (W g * p g + W g * q g) ∂μ := by
        rw [lintegral_const_mul'' _ ((hW.mul hp).add (hW.mul hq)).aemeasurable]
      _ = coeff *
          ((∫⁻ g, W g * p g ∂μ) +
            ∫⁻ g, W g * q g ∂μ) := by
        rw [lintegral_add_left (hW.mul hp)]
  change
    (∫⁻ g, W g
        ∂C.singleLinkConditionalLeftResidualMeasure A B target) +
      (∫⁻ g, W g
        ∂C.singleLinkConditionalRightResidualMeasure A B target) ≤
      coeff *
        ((∫⁻ g, W g ∂C.singleLinkConditionalMeasure A target) +
          ∫⁻ g, W g ∂C.singleLinkConditionalMeasure B target)
  rw [hLeft, hRight, hA, hB]
  rw [← hRawLeft, ← hRawRight]
  simpa [μ, W, lD, rD, p, q, coeff] using hRaw

/-- RMS likelihood-ratio transport for the exact one-link overlap coupling.
This is the central replacement for the old sup-norm overlap-energy estimate. -/
theorem
    continuous_compact_oriented_singleLinkConditionalOverlapCoupling_centeredSquare_lintegral_le_two_mul_coefficient
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (K : ℝ)
    (hK : 1 ≤ K)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          K * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          K * C.singleLinkConditionalDensityReal A target g)
    (X : C.base.Gauge → ℝ)
    (hX : StronglyMeasurable X)
    (center : ℝ) :
    (∫⁻ z,
      ENNReal.ofReal ((X z.1 - X z.2) ^ 2)
      ∂C.singleLinkConditionalOverlapCouplingMeasure A B target) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
          ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
              ∂C.singleLinkConditionalMeasure A target) +
            ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
              ∂C.singleLinkConditionalMeasure B target) := by
  have hOverlap :=
    continuous_compact_oriented_singleLinkConditionalOverlapCoupling_centeredSquare_lintegral_le_two_residual
      C A B target X hX center
  have hResidual :=
    continuous_compact_oriented_singleLinkConditionalResidualMeasure_centeredSquare_sum_lintegral_le_coefficient
      C A B target K hK hRatio X hX center
  calc
    (∫⁻ z,
      ENNReal.ofReal ((X z.1 - X z.2) ^ 2)
      ∂C.singleLinkConditionalOverlapCouplingMeasure A B target) ≤
        (2 : ℝ≥0∞) *
          ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
              ∂C.singleLinkConditionalLeftResidualMeasure A B target) +
            ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
              ∂C.singleLinkConditionalRightResidualMeasure A B target) :=
      hOverlap
    _ ≤
        (2 : ℝ≥0∞) *
          (ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
            ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
                ∂C.singleLinkConditionalMeasure A target) +
              ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
                ∂C.singleLinkConditionalMeasure B target)) := by
      gcongr
    _ =
        (2 : ℝ≥0∞) *
          ENNReal.ofReal (HaarLikelihoodRatioInfluence.coefficient K) *
            ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
                ∂C.singleLinkConditionalMeasure A target) +
              ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
                ∂C.singleLinkConditionalMeasure B target) := by
      rw [mul_assoc]

/-- Log-density oscillation specialization of the RMS overlap-coupling energy
bound. -/
theorem
    continuous_compact_oriented_singleLinkConditionalOverlapCoupling_centeredSquare_lintegral_le_two_mul_compactHaarOscillationInfluence
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hRatio : ∀ g : C.base.Gauge,
      C.singleLinkConditionalDensityReal A target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal B target g ∧
        C.singleLinkConditionalDensityReal B target g ≤
          Real.exp R * C.singleLinkConditionalDensityReal A target g)
    (X : C.base.Gauge → ℝ)
    (hX : StronglyMeasurable X)
    (center : ℝ) :
    (∫⁻ z,
      ENNReal.ofReal ((X z.1 - X z.2) ^ 2)
      ∂C.singleLinkConditionalOverlapCouplingMeasure A B target) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal (compactHaarOscillationInfluence R) *
          ((∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
              ∂C.singleLinkConditionalMeasure A target) +
            ∫⁻ g, ENNReal.ofReal ((X g - center) ^ 2)
              ∂C.singleLinkConditionalMeasure B target) := by
  simpa [compactHaarOscillationInfluence] using
    continuous_compact_oriented_singleLinkConditionalOverlapCoupling_centeredSquare_lintegral_le_two_mul_coefficient
      C A B target (Real.exp R) (Real.one_le_exp hR) hRatio X hX center

end

end MGAP4D.MathlibAnalytic
