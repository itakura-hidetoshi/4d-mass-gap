import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointHalfDensityUniformHarnackCoercivityV5_LV
import Mathlib.Tactic

/-!
# P4-Q2-LW — exact genuine Wilson transfer-normalization scaling

LV proves that each *actual* JH GI bounded Hilbert functional is at most
  ||T_{H,b}||⁻¹ exp(8b) [exp(16b)-exp(-16b)].
We now separate this transfer normalization ALGORITHMICALLY from the
same genuine interacting-Wilson and Gauss-law physical detector.

Set t=||T||>0. Define the transfer-COMPENSATED presentation as
  Gbar(e,z)=t • G(e,z).
JH's original Riesz identity, and only algebra, give exactly
  Gbar(e,z) = -s(z) • originalFiberMoment(e,z).
No physical source, Wilson posterior, link, boundary or transfer operator
is replaced. Gbar is just a scalar re-presentation of the ACTUAL GI map.

Consequences proved *for the original physical Wilson sources*:
  ||Gbar(e,z)|| <= E_b := exp(8b)(exp(16b)-exp(-16b)),
  Δbar_total = t² Δ_total,     Δbar_p = t² Δ_p,
  Fbar_p = t² F_p,            κbar_p = t² κ_p   (when Δ_p != 0).

The exact rescaled finite-H physical source inequality and the normalized
global determinant floor then read
  κbar_p (x²+y²) <= (t G_1(ψ_xy))²+(t G_2(ψ_xy))²,
  κbar_p >= Δbar_total² / (10 N_H² E_b²).

CRUCIAL OBSTRUCTION: this is NOT an H-uniform coercivity assertion for
the original physical G. Reverting to its actual coefficient requires
  κ_p=t⁻² κbar_p,
and the true Δbar_total/N_H may still decay with increasing H. No
transfer-normalization cancellation has been claimed for that remaining
physical factor. Original H1-C3 closure and continuum mass gap are OPEN.

No synthetic rank hypothesis, artificial source, independent-Haar
replacement for interacting posteriors, Dobrushin, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LW_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LW_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LW_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LW_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LW_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) b hb
local notation "G" => p4Q2JH_originalGIResponseCLM H b hb
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- Literal transfer operator norm in JH, not an external normalizer. -/
noncomputable def p4Q2LW_originalPhysicalTransferNorm : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb‖

local notation "tN" => p4Q2LW_originalPhysicalTransferNorm H b hb

theorem p4Q2LW_originalPhysicalTransferNorm_pos :
    0 < tN := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) b hb

/-- Only the H-independent Wilson kernel, true conditional-posterior
contrast and original SU(2) one-link joint-half-density Harnack factor. -/
noncomputable def p4Q2LW_originalHarnackContrastScale (b : ℝ) : ℝ :=
  Real.exp (8 * b) * p4Q2LS_originalPosteriorContrastEnvelope b

local notation "E" => p4Q2LW_originalHarnackContrastScale b

theorem p4Q2LW_originalHarnackContrastScale_nonneg
    (hpos : 0 ≤ b) :
    0 ≤ E := by
  exact mul_nonneg (Real.exp_pos _).le
    (p4Q2LS_originalPosteriorContrastEnvelope_nonneg b hpos)

theorem p4Q2LW_originalHarnackContrastScale_pos
    (hpos : 0 < b) :
    0 < E := by
  have hlt : -16 * b < 16 * b := by nlinarith
  have he : Real.exp (-16 * b) < Real.exp (16 * b) :=
    Real.exp_lt_exp.mpr hlt
  unfold p4Q2LW_originalHarnackContrastScale
    p4Q2LS_originalPosteriorContrastEnvelope
  exact mul_pos (Real.exp_pos _) (sub_pos.mpr he)

/-- The compensated response remains *literally* the original
JH interacting-Wilson detector, multiplied by its OWN transfer norm. -/
noncomputable def p4Q2LW_originalTransferCompensatedGIResponse
    (e : Link) (z : Cfg × Cfg) :
    Lp ℝ 2 haar →L[ℝ] ℝ :=
  tN • G e z

local notation "Q" => p4Q2LW_originalTransferCompensatedGIResponse H b hb

/-- JH's exact original Riesz formula after algebraic cancellation of
the positive transfer norm (no alteration of the original physical
source or interacting Wilson posterior). -/
theorem p4Q2LW_originalCompensatedGI_eq_originalRiesz
    (e : Link) (z : Cfg × Cfg) :
    Q e z =
      (-(s z)) • p4Q2JH_originalFiberMomentCLM H b hb e z := by
  let M := p4Q2JH_originalFiberMomentCLM H b hb e z
  have ht : tN ≠ 0 := (p4Q2LW_originalPhysicalTransferNorm_pos H b hb).ne'
  ext f
  change tN * ((-tN⁻¹ * s z) * M f) = (-(s z)) * M f
  field_simp [ht]

/-- The exact compensated REAL JH bounded-functional operator norm
has no remaining transfer or true-half-density factor. -/
theorem p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast
    (e : Link) (z : Cfg × Cfg) :
    ‖Q e z‖ ≤ E := by
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  have hGI := p4Q2LV_originalGIResponse_norm_le_uniformContext H b hb e z
  change ‖G e z‖ ≤ tN⁻¹ * E at hGI
  change ‖tN • G e z‖ ≤ E
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc
    tN * ‖G e z‖ ≤ tN * (tN⁻¹ * E) :=
      mul_le_mul_of_nonneg_left hGI ht.le
    _ = E := by field_simp [ne_of_gt ht]

/-- The TRUE physical two-context spatial Wilson determinant, with
the SAME two original GI rows compensated by their shared norm. -/
noncomputable def p4Q2LW_originalCompensatedSpatialGIMinor
    (e e' : Link) (z z' : Cfg × Cfg) : ℝ :=
  Q e z (L (1 : C(Cfg, ℝ))) *
    Q e' z' (L (p4Q2JI_actualSpatialWilsonContinuous H)) -
  Q e z (L (p4Q2JI_actualSpatialWilsonContinuous H)) *
    Q e' z' (L (1 : C(Cfg, ℝ)))

theorem p4Q2LW_originalCompensatedSpatialGIMinor_eq_sq_mul_original
    (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2LW_originalCompensatedSpatialGIMinor H b hb e e' z z' =
      tN^2 * p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' := by
  let a := G e z (L (1 : C(Cfg, ℝ)))
  let q := G e z (L (p4Q2JI_actualSpatialWilsonContinuous H))
  let c := G e' z' (L (1 : C(Cfg, ℝ)))
  let d := G e' z' (L (p4Q2JI_actualSpatialWilsonContinuous H))
  change (tN * a) * (tN * d) - (tN * q) * (tN * c) =
    tN^2 * (a * d - q * c)
  ring

/-- An ACTUAL single spatial plaquette (LO) with compensated detector
rows, never a reselected plaquette or synthetic physical source. -/
noncomputable def p4Q2LW_originalCompensatedLocalGIMinor
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) : ℝ :=
  Q e z (L (1 : C(Cfg, ℝ))) *
    Q e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p)) -
  Q e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p)) *
    Q e' z' (L (1 : C(Cfg, ℝ)))

theorem p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    p4Q2LW_originalCompensatedLocalGIMinor H b hb e e' z z' p =
      tN^2 * p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p := by
  let a := G e z (L (1 : C(Cfg, ℝ)))
  let q := G e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  let c := G e' z' (L (1 : C(Cfg, ℝ)))
  let d := G e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  change (tN * a) * (tN * d) - (tN * q) * (tN * c) =
    tN^2 * (a * d - q * c)
  ring

/-- Four actual original physical JH evaluations, with shared
transfer-scaling; never a new detector matrix with postulated rank. -/
noncomputable def p4Q2LW_originalCompensatedLocalGIFrobeniusSq
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) : ℝ :=
  (Q e z (L (1 : C(Cfg, ℝ))))^2 +
  (Q e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p)))^2 +
  (Q e' z' (L (1 : C(Cfg, ℝ))))^2 +
  (Q e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p)))^2

theorem p4Q2LW_originalCompensatedLocalGIFrobeniusSq_eq_sq_mul_original
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    p4Q2LW_originalCompensatedLocalGIFrobeniusSq H b hb e e' z z' p =
      tN^2 * p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p := by
  let a := G e z (L (1 : C(Cfg, ℝ)))
  let q := G e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  let c := G e' z' (L (1 : C(Cfg, ℝ)))
  let d := G e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  change (tN * a)^2 + (tN * q)^2 +
    (tN * c)^2 + (tN * d)^2 =
      tN^2 * (a^2 + q^2 + c^2 + d^2)
  ring

/-- For the SAME actual original Wilson plaquette, compensation turns
LV's Frobenius denominator into a factor-free bound 10 E_b². -/
theorem p4Q2LW_originalCompensatedLocalGIFrobeniusSq_le_ten_contrastSq
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    p4Q2LW_originalCompensatedLocalGIFrobeniusSq H b hb e e' z z' p ≤
      10 * E^2 := by
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  have hF :=
    p4Q2LV_originalLocalGIFrobeniusSq_le_ten_uniformEnvelopeSq
      H b hb e e' z z' p
  change
    p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p ≤
      10 * (tN⁻¹ * E)^2 at hF
  rw [p4Q2LW_originalCompensatedLocalGIFrobeniusSq_eq_sq_mul_original]
  calc
    tN^2 * p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p ≤
      tN^2 * (10 * (tN⁻¹ * E)^2) :=
        mul_le_mul_of_nonneg_left hF (sq_nonneg tN)
    _ = 10 * E^2 := by field_simp [ne_of_gt ht]

/-- Ratio of the EXACT same genuine compensated minor and Frobenius
sum, which only changes the output units of the original GI response. -/
noncomputable def p4Q2LW_originalCompensatedLocalGICoefficient
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) : ℝ :=
  (p4Q2LW_originalCompensatedLocalGIMinor H b hb e e' z z' p)^2 /
    p4Q2LW_originalCompensatedLocalGIFrobeniusSq H b hb e e' z z' p

/-- EXACT scaling law of the genuine physical local coercivity constant:
two-row determinants scale quadratically, their squared determinants
quartically, and Frobenius-square quadratically. There remains exactly
one factor ||T||²; it does NOT disappear from the physical κ. -/
theorem p4Q2LW_originalCompensatedLocalGICoefficient_eq_sq_mul_original
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    p4Q2LW_originalCompensatedLocalGICoefficient H b hb e e' z z' p =
      tN^2 * p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p := by
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  have hF := p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
    H b hb e e' z z' p hminor
  unfold p4Q2LW_originalCompensatedLocalGICoefficient
  rw [p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original,
      p4Q2LW_originalCompensatedLocalGIFrobeniusSq_eq_sq_mul_original]
  let det := p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p
  let fr := p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p
  change (tN^2 * det)^2 / (tN^2 * fr) = tN^2 * (det^2 / fr)
  field_simp [ne_of_gt ht, ne_of_gt hF]

/-- The ORIGINAL two interacting Wilson expectation-gap responses on
the SAME Gauss-law physical plane remain exactly coercive under the
canonical transfer scaling. No new source plane or rank is assumed. -/
theorem p4Q2LW_originalCompensatedPhysicalLocalTwoSource_coercive
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    0 < p4Q2LW_originalCompensatedLocalGICoefficient
      H b hb e e' z z' p ∧
    ∀ x y : ℝ,
      p4Q2LW_originalCompensatedLocalGICoefficient
        H b hb e e' z z' p * (x^2 + y^2) ≤
        (tN * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
        (tN * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  obtain ⟨hκ, hResponse⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hminor
  rw [p4Q2LW_originalCompensatedLocalGICoefficient_eq_sq_mul_original
    H b hb e e' z z' p hminor]
  constructor
  · exact mul_pos (sq_pos_of_pos ht) hκ
  · intro x y
    let κ : ℝ := p4Q2LO_originalLocalGIQuantitativeCoefficient
      H b hb e e' z z' p
    let a : ℝ := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z
    let c : ℝ := p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
      H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z'
    have hOriginal : κ * (x^2 + y^2) ≤ a^2 + c^2 := hResponse x y
    change (tN^2 * κ) * (x^2 + y^2) ≤ (tN * a)^2 + (tN * c)^2
    calc
      (tN^2 * κ) * (x^2 + y^2) =
          tN^2 * (κ * (x^2 + y^2)) := by ring
      _ ≤ tN^2 * (a^2 + c^2) :=
        mul_le_mul_of_nonneg_left hOriginal (sq_nonneg tN)
      _ = (tN * a)^2 + (tN * c)^2 := by ring

/-- With positive genuine coupling, the original LV normalized floor
scales to the fully transfer-COMPENSATED determinant estimate. Original
physical κ still has a remaining inverse transfer-norm SQUARE on return.
This is an exact equality of scaling, NOT a uniform-in-H assertion. -/
theorem p4Q2LW_originalCompensatedLocalGI_ge_compensatedGlobal_floor
    (hpos : 0 < b) (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0)
    (hcount : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ))
    (hAvg : |p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'| /
      (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
      |p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p|) :
    (p4Q2LW_originalCompensatedSpatialGIMinor H b hb e e' z z')^2 /
      ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
        (10 * E^2)) ≤
      p4Q2LW_originalCompensatedLocalGICoefficient
        H b hb e e' z z' p := by
  let total : ℝ := p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'
  let count : ℝ := (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
  let κ : ℝ := p4Q2LO_originalLocalGIQuantitativeCoefficient
    H b hb e e' z z' p
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  have hE := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hLV := p4Q2LV_originalLocalGI_coercivity_ge_global_uniformContext_floor
    H b hb e e' z z' p hminor hcount hAvg
  change total^2 / (count^2 * (10 * (tN⁻¹ * E)^2)) ≤ κ at hLV
  have hRewrite :
      (tN^2 * total)^2 / (count^2 * (10 * E^2)) =
        tN^2 * (total^2 / (count^2 * (10 * (tN⁻¹ * E)^2))) := by
    field_simp [ne_of_gt ht, ne_of_gt hcount, ne_of_gt hE]
  rw [p4Q2LW_originalCompensatedSpatialGIMinor_eq_sq_mul_original,
      p4Q2LW_originalCompensatedLocalGICoefficient_eq_sq_mul_original
        H b hb e e' z z' p hminor]
  change (tN^2 * total)^2 / (count^2 * (10 * E^2)) ≤ tN^2 * κ
  rw [hRewrite]
  exact mul_le_mul_of_nonneg_left hLV (sq_nonneg tN)

/-- ORIGINAL finite-volume LP witness transported to the compensated
presentation *without changing the physical sources/posteriors/plaquette*.
Any claim of H-uniformity requires NEW ANALYTIC PROOFS about the actual
normalized global determinant per plaquette and the transfer norm. -/
theorem p4Q2LW_originalPhysicalLocalGI_exists_compensated_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < p4Q2LW_originalCompensatedLocalGICoefficient
        H b hb e e' z z' p ∧
      (p4Q2LW_originalCompensatedSpatialGIMinor
        H b hb e e' z z')^2 /
        ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
          (10 * E^2)) ≤
        p4Q2LW_originalCompensatedLocalGICoefficient
          H b hb e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LW_originalCompensatedLocalGICoefficient
          H b hb e e' z z' p * (x^2 + y^2) ≤
          (tN * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (tN * p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hpos e e' left₀ right₀
  have hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  obtain ⟨hκ, hResponse⟩ :=
    p4Q2LW_originalCompensatedPhysicalLocalTwoSource_coercive
      H b hb e e' z z' p hlocal
  have hFloor :=
    p4Q2LW_originalCompensatedLocalGI_ge_compensatedGlobal_floor
      H b hb hpos e e' z z' p hlocal hn hAvg
  exact ⟨z, z', p, hp, hn, hκ, hFloor, hResponse⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalPhysicalTransferNorm_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalHarnackContrastScale_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedGI_eq_originalRiesz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedSpatialGIMinor_eq_sq_mul_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedLocalGIFrobeniusSq_eq_sq_mul_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedLocalGIFrobeniusSq_le_ten_contrastSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedLocalGICoefficient_eq_sq_mul_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedPhysicalLocalTwoSource_coercive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalCompensatedLocalGI_ge_compensatedGlobal_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LW_originalPhysicalLocalGI_exists_compensated_floor
