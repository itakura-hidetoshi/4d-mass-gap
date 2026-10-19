import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCountControlledLocalPhysicalGICoercivityV5_LQ
import Mathlib.Tactic

/-!
# P4-Q2-LR — true SU(2) local physical GI Frobenius upper bound

LQ established a finite-volume true ORIGINAL interacting-Wilson-posterior
Gauss-law physical Hilbert detector coefficient with lower bound
    Delta_global^2 / (N_H^2 * F_p) <= kappa_p,
where F_p is the exact Frobenius-square of the two actual JH detectors
evaluated on the genuine physical constant unit and local Wilson source.

We now bound this REAL denominator using only:
* the original local SU(2) Wilson energy 0 <= W_p <= 2,
* the original gauge-invariant physical multiplication operator norm bound,
* the literal normalized probability-Haar constant source ||U|| = 1,
* genuine JH continuous-linear-map operator norms at TWO actual
  interacting Wilson boundary contexts.

The resulting exact estimate is
    F_p <= 5 * (||G_e,z||^2 + ||G_e',z'||^2).
At the LP/LQ-proved true nonzero local witness, this denominator bound
is strictly positive, yielding the explicit finite-H inequality
    Delta_global^2 /
       (5 * N_H^2 * (||G_e,z||^2 + ||G_e',z'||^2)) <= kappa_p
together with coercivity on EVERY genuine physical Gauss-law source
    x U + y W_p U.

The local observable bound 2 is UNIFORM in spatial volume H, but
the actual frozen JH operator norms and original global minor need NOT
be uniform in H. This does not establish H1-C3 strong-limit closure,
the continuum Yang–Mills construction, or a positive mass gap.
No independent-Haar posterior replacement, synthetic detector/rank,
Dobrushin, sorry/admit or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Squaring a nonnegative upper bound on the real absolute value. -/
private theorem p4Q2LR_sq_le_of_abs_le
    (x B : ℝ) (h : |x| ≤ B) : x^2 ≤ B^2 := by
  have hpos : 0 ≤ |x| := abs_nonneg _
  have hB : 0 ≤ B := le_trans hpos h
  have hprod : 0 ≤ (B - |x|) * (B + |x|) :=
    mul_nonneg (sub_nonneg.mpr h) (add_nonneg hB hpos)
  have hs : |x|^2 ≤ B^2 := by nlinarith [hprod]
  simpa only [sq_abs] using hs

end GroundStatePosteriorJoint

local instance p4Q2LR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "G" => p4Q2JH_originalGIResponseCLM H

/-- The genuine bounded continuous SU(2) plaquette Wilson-energy
observable is globally bounded by TWO, independently of H and p. -/
theorem p4Q2LR_originalLocalPlaquetteBounded_norm_le_two
    (p : Plaq) :
    ‖p4Q2LO_originalLocalPlaquetteBounded H p‖ ≤ 2 := by
  apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 2)).2
  intro A
  change ‖specialUnitaryWilsonPlaquetteEnergy 2
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)‖ ≤ 2
  rw [Real.norm_eq_abs, abs_of_nonneg
    (specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) _)]
  exact specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) _

/-- The true Gauss-law constant unit is normalized by the ORIGINAL
product SU(2) Haar probability measure, without an invented vacuum. -/
theorem p4Q2LR_originalPhysicalUnit_norm :
    ‖(U : Phys)‖ = 1 := by
  change ‖Lp.const 2 haar (1 : ℝ)‖ = 1
  simpa [measureReal_def] using
    (Lp.norm_const (μ := haar) (p := 2) (c := (1 : ℝ)) (by norm_num))

/-- The local physical Gauss-law multiplication source has Hilbert norm
at most TWO, via the EXISTING physically gauge-invariant bounded
multiplication operator. No independent posterior is used. -/
theorem p4Q2LR_originalLocalPlaquettePhysicalSource_norm_le_two
    (p : Plaq) :
    ‖(p4Q2LO_originalLocalPlaquettePhysicalSource H p : Phys)‖ ≤ 2 := by
  let a := p4Q2LO_originalLocalPlaquetteBounded H p
  let M : Phys →L[ℝ] Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
      H 2 a (p4Q2LO_originalLocalPlaquetteBounded_gaugeInvariant H p)
  have hM : ‖M‖ ≤ ‖a‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator_norm_le
      H 2 a (p4Q2LO_originalLocalPlaquetteBounded_gaugeInvariant H p)
  change ‖M (U : Phys)‖ ≤ 2
  calc
    ‖M (U : Phys)‖ ≤ ‖M‖ * ‖(U : Phys)‖ := M.le_opNorm _
    _ = ‖M‖ := by rw [p4Q2LR_originalPhysicalUnit_norm H, mul_one]
    _ ≤ ‖a‖ := hM
    _ ≤ 2 := p4Q2LR_originalLocalPlaquetteBounded_norm_le_two H p

/-- The same SU(2) bound stated for the exact ORIGINAL continuous
local Wilson source embedded in reference spatial Haar-L². -/
theorem p4Q2LR_originalLocalPlaquette_toLp_norm_le_two
    (p : Plaq) :
    ‖L (p4Q2LO_originalLocalPlaquetteContinuous H p)‖ ≤ 2 := by
  rw [← p4Q2LO_originalLocalPlaquettePhysicalSource_coe_eq_toLp H p]
  change ‖(p4Q2LO_originalLocalPlaquettePhysicalSource H p : Phys)‖ ≤ 2
  exact p4Q2LR_originalLocalPlaquettePhysicalSource_norm_le_two H p

/-- The constant one has the same original probability-Haar L² unit norm. -/
theorem p4Q2LR_originalHaarUnit_norm :
    ‖L (1 : C(Cfg, ℝ))‖ = 1 := by
  rw [← p4Q2JU_originalPhysicalUnit_coe_eq_toLp H]
  change ‖(U : Phys)‖ = 1
  exact p4Q2LR_originalPhysicalUnit_norm H

/-- One true original JH GI detector is bounded on the constant unit
by its own continuous-linear-map operator norm. -/
private theorem p4Q2LR_originalGI_unit_abs_le_opNorm
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    |G b hb e z (L (1 : C(Cfg, ℝ)))| ≤ ‖G b hb e z‖ := by
  have h := (G b hb e z).le_opNorm (L (1 : C(Cfg, ℝ)))
  simpa only [Real.norm_eq_abs, p4Q2LR_originalHaarUnit_norm H, mul_one] using h

/-- The ORIGINAL true interacting-Wilson-posterior GI detector on
the local SU(2) plaquette source is bounded by TWO operator norms. -/
private theorem p4Q2LR_originalGI_local_abs_le_two_opNorm
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg)
    (p : Plaq) :
    |G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))| ≤
      ‖G b hb e z‖ * 2 := by
  have h := (G b hb e z).le_opNorm
    (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  calc
    |G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))| =
        ‖G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ‖G b hb e z‖ *
        ‖L (p4Q2LO_originalLocalPlaquetteContinuous H p)‖ := h
    _ ≤ ‖G b hb e z‖ * 2 :=
      mul_le_mul_of_nonneg_left
        (p4Q2LR_originalLocalPlaquette_toLp_norm_le_two H p) (norm_nonneg _)

/-- Fundamental genuinely physical Frobenius denominator estimate:
the four TRUE original GI matrix entries are evaluated by two
bounded JH functionals on U and W_p U. Their operator norms give
the sharp elementary constant 1²+2² = FIVE, uniformly in plaquette
support and finite spatial volume. No detector normalization premise. -/
theorem p4Q2LR_originalLocalGIFrobeniusSq_le_five_opNormSq
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq) :
    p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p ≤
      5 * (‖G b hb e z‖^2 + ‖G b hb e' z'‖^2) := by
  let a : ℝ := G b hb e z (L (1 : C(Cfg, ℝ)))
  let q : ℝ := G b hb e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  let c : ℝ := G b hb e' z' (L (1 : C(Cfg, ℝ)))
  let d : ℝ := G b hb e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  have ha : a^2 ≤ ‖G b hb e z‖^2 :=
    p4Q2LR_sq_le_of_abs_le a _ (p4Q2LR_originalGI_unit_abs_le_opNorm H b hb e z)
  have hq0 : q^2 ≤ (‖G b hb e z‖ * 2)^2 :=
    p4Q2LR_sq_le_of_abs_le q _ (p4Q2LR_originalGI_local_abs_le_two_opNorm H b hb e z p)
  have hc : c^2 ≤ ‖G b hb e' z'‖^2 :=
    p4Q2LR_sq_le_of_abs_le c _ (p4Q2LR_originalGI_unit_abs_le_opNorm H b hb e' z')
  have hd0 : d^2 ≤ (‖G b hb e' z'‖ * 2)^2 :=
    p4Q2LR_sq_le_of_abs_le d _ (p4Q2LR_originalGI_local_abs_le_two_opNorm H b hb e' z' p)
  change a^2 + q^2 + c^2 + d^2 ≤
    5 * (‖G b hb e z‖^2 + ‖G b hb e' z'‖^2)
  nlinarith [ha, hq0, hc, hd0]

/-- With a truly nonzero local GI determinant, the authentic JH operator
norms at these original two contexts cannot both vanish. -/
theorem p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p ≠ 0) :
    0 < 5 * (‖G b hb e z‖^2 + ‖G b hb e' z'‖^2) := by
  exact lt_of_lt_of_le
    (p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
      H b hb e e' z z' p hminor)
    (p4Q2LR_originalLocalGIFrobeniusSq_le_five_opNormSq
      H b hb e e' z z' p)

/-- Exact new quantitative lower bound independent of local source
Frobenius entries: the ORIGINAL global minor squared, squared genuine
spatial plaquette count, and TWO actual interacting-posterior
GI bounded-functional operator norms are the only remaining factors. -/
theorem p4Q2LR_originalLocalGI_coercivity_ge_global_opNorm_floor
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p ≠ 0)
    (hcount : 0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ))
    (hAvg : |p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'| /
       (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
       |p4Q2LO_originalLocalPlaquetteGIMinor H b hb e e' z z' p|) :
    (p4Q2JI_originalGISpatialActionMinor H b hb e e' z z')^2 /
      ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
        (5 * (‖G b hb e z‖^2 + ‖G b hb e' z'‖^2))) ≤
      p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p := by
  let total := p4Q2JI_originalGISpatialActionMinor H b hb e e' z z'
  let n : ℝ := (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
  let F : ℝ := p4Q2LO_originalLocalGIFrobeniusSq H b hb e e' z z' p
  let C : ℝ := 5 * (‖G b hb e z‖^2 + ‖G b hb e' z'‖^2)
  have hF : 0 < F :=
    p4Q2LQ_originalLocalGIFrobeniusSq_pos_of_minor_ne
      H b hb e e' z z' p hminor
  have hFC : F ≤ C := p4Q2LR_originalLocalGIFrobeniusSq_le_five_opNormSq
    H b hb e e' z z' p
  have hC : 0 < C := lt_of_lt_of_le hF hFC
  have hCount : 0 < n := hcount
  have hn2 : 0 < n^2 := sq_pos_of_pos hCount
  have hFden : 0 < n^2 * F := mul_pos hn2 hF
  have hCden : 0 < n^2 * C := mul_pos hn2 hC
  have hden : n^2 * F ≤ n^2 * C :=
    mul_le_mul_of_nonneg_left hFC (sq_nonneg n)
  have hDiv : total^2 / (n^2 * C) ≤ total^2 / (n^2 * F) :=
    (div_le_div_iff₀ hCden hFden).2
      (mul_le_mul_of_nonneg_left hden (sq_nonneg total))
  have hLQ :=
    p4Q2LQ_originalLocalGI_coercivity_ge_global_squared_floor
      H b hb e e' z z' p hminor hcount hAvg
  exact le_trans hDiv hLQ

/-- LQ plus the genuine local SU(2) 0-2 energy norm establishes
unconditional finite-H physical GI coercivity with a new explicit
norm-controlled denominator. All sources/posteriors and contexts are
the unchanged ORIGINAL Wilson constructions. -/
theorem p4Q2LR_originalPhysicalLocalGI_exists_opNorm_floor
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < 5 * (‖G b hb.le e z‖^2 + ‖G b hb.le e' z'‖^2) ∧
      0 < p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb.le e e' z z' p ∧
      (p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z')^2 /
        ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
          (5 * (‖G b hb.le e z‖^2 + ‖G b hb.le e' z'‖^2))) ≤
        p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb.le e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb.le e e' z z' p *
          (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb.le
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb.le
            (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hb e e' left₀ right₀
  have hLocal : p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  have hN := p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
    H b hb.le e e' z z' p hLocal
  obtain ⟨hκ, hBound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb.le e e' z z' p hLocal
  have hFloor := p4Q2LR_originalLocalGI_coercivity_ge_global_opNorm_floor
    H b hb.le e e' z z' p hLocal hn hAvg
  exact ⟨z, z', p, hp, hn, hN, hκ, hFloor, hBound⟩

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalLocalPlaquetteBounded_norm_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalPhysicalUnit_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalLocalPlaquettePhysicalSource_norm_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalLocalPlaquette_toLp_norm_le_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalHaarUnit_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalLocalGIFrobeniusSq_le_five_opNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalGI_opNormSq_sum_pos_of_local_minor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalLocalGI_coercivity_ge_global_opNorm_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LR_originalPhysicalLocalGI_exists_opNorm_floor