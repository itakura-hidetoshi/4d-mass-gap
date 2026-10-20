import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalGIMeanVarianceDecompositionV5_LZ
import Mathlib.Tactic

/-!
# P4-Q2-MA — genuine Wilson GI local-minor uniform upper energy

LZ decomposes the actual transfer-compensated GI squared local-minor
energy on every genuine SU(2) spatial plaquette into mean²+variance.
The crucial missing H1-C3 analytic result is a uniform strictly positive
LOWER bound for its true density Q/N, not a bound on signs.

This module formalizes the matching finite-H UPPER estimate, without
replacing any interacting-Wilson posterior or Gauss-law source.

For every volume H, coupling b >= 0, real physical link pair e,e',
actual boundary contexts z,z', and original plaquette p:

* The original physical constant source has Haar-L² norm ONE, while
  the actual gauge-invariant local plaquette Wilson-energy source
  has Haar-L² norm at most TWO (already proved by LR).
* LW establishes ||t_H G(e,z)|| <= E_b, where t_H=||T_H|| is
  the *actual* physical transfer norm, and
  E_b=exp(8b) (exp(16b)-exp(-16b)).
* Therefore the genuine compensated two-context 2x2 determinant
  satisfies |DeltaBar_p| <= 4 E_b².
* Hence the actual noncancelling square-energy has uniform density
  Q_H/N_H <= 16 E_b^4.
* LZ's genuine spatial local-minor variance satisfies
  0 <= Var_H <= 16 E_b^4.
* At the same authentic LY-selected real contexts/plaquette for b>0,
  the original physical GI coercivity coefficient has the exact
  mean-plus-variance floor, with finite-H energy density in
  (0,16 E_b^4] and variance in [0,16 E_b^4].

The upper estimates are uniform in H but are NOT uniform positive
lower estimates: Q_H/N_H may tend to zero. Nothing here closes H1-C3,
the continuum Yang-Mills construction, or its positive mass gap.

No artificial detector, physical source, rank, independent Haar
posterior, Dobrushin argument, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ
local notation "Gbar" => p4Q2LW_originalTransferCompensatedGIResponse H b hb
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "V" => p4Q2LZ_originalCompensatedLocalGIVariance H b hb
local notation "m" => p4Q2LZ_originalCompensatedLocalGIMean H b hb
local notation "kappa" => p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb

/-- Exact original transfer-COMPENSATED JH GI response on the genuine
unit Gauss-law source, bounded uniformly in finite volume H. -/
theorem p4Q2MA_originalCompensatedGI_unit_abs_le_contrast
    (e : Link) (z : Cfg × Cfg) :
    |Gbar e z (L (1 : C(Cfg, ℝ)))| ≤ E := by
  have hOp :=
    (Gbar e z).le_opNorm (L (1 : C(Cfg, ℝ)))
  have hUnit := p4Q2LR_originalHaarUnit_norm H
  rw [Real.norm_eq_abs, hUnit, mul_one] at hOp
  exact hOp.trans
    (p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast H b hb e z)

/-- The actual SU(2) Wilson plaquette Gauss-law source has norm at most
two, so its original JH GI response has absolute value at most 2 E_b. -/
theorem p4Q2MA_originalCompensatedGI_local_abs_le_two_contrast
    (e : Link) (z : Cfg × Cfg) (p : Plaq) :
    |Gbar e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))| ≤
      E * 2 := by
  let sourceFn : C(Cfg, ℝ) := p4Q2LO_originalLocalPlaquetteContinuous H p
  let x := L sourceFn
  let G := Gbar e z
  have hOp : ‖G x‖ ≤ ‖G‖ * ‖x‖ := G.le_opNorm x
  have hLocal : ‖x‖ ≤ 2 :=
    p4Q2LR_originalLocalPlaquette_toLp_norm_le_two H p
  have hG : ‖G‖ ≤ E :=
    p4Q2LW_originalCompensatedGI_norm_le_HarnackContrast H b hb e z
  change |G x| ≤ E * 2
  calc
    |G x| = ‖G x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖G‖ * ‖x‖ := hOp
    _ ≤ ‖G‖ * 2 :=
      mul_le_mul_of_nonneg_left hLocal (norm_nonneg G)
    _ ≤ E * 2 :=
      mul_le_mul_of_nonneg_right hG (by norm_num)

/-- Original interacting-Wilson physical local 2x2 determinant, after
nothing but the original transfer compensation, is bounded by 4 E_b²,
uniformly in spatial H, actual links, contexts and plaquette p. -/
theorem p4Q2MA_originalCompensatedLocalGIMinor_abs_le_four_contrastSq
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    |d e e' z z' p| ≤ 4 * E^2 := by
  let a : ℝ := Gbar e z (L (1 : C(Cfg, ℝ)))
  let q : ℝ := Gbar e z (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  let c : ℝ := Gbar e' z' (L (1 : C(Cfg, ℝ)))
  let v : ℝ := Gbar e' z' (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
  have ha : |a| ≤ E :=
    p4Q2MA_originalCompensatedGI_unit_abs_le_contrast H b hb e z
  have hq : |q| ≤ E * 2 :=
    p4Q2MA_originalCompensatedGI_local_abs_le_two_contrast H b hb e z p
  have hc : |c| ≤ E :=
    p4Q2MA_originalCompensatedGI_unit_abs_le_contrast H b hb e' z'
  have hv : |v| ≤ E * 2 :=
    p4Q2MA_originalCompensatedGI_local_abs_le_two_contrast H b hb e' z' p
  have hE : 0 ≤ E :=
    p4Q2LW_originalHarnackContrastScale_nonneg b hb
  have hE2 : 0 ≤ E * 2 := mul_nonneg hE (by norm_num)
  have hav : |a * v| ≤ E * (E * 2) := by
    calc
      |a * v| = |a| * |v| := abs_mul _ _
      _ ≤ E * (E * 2) := mul_le_mul ha hv (abs_nonneg _) hE
  have hqc : |q * c| ≤ (E * 2) * E := by
    calc
      |q * c| = |q| * |c| := abs_mul _ _
      _ ≤ (E * 2) * E := mul_le_mul hq hc (abs_nonneg _) hE2
  change |a * v - q * c| ≤ 4 * E^2
  calc
    |a * v - q * c| ≤ |a * v| + |q * c| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (a * v) (-(q * c)))
    _ ≤ E * (E * 2) + (E * 2) * E :=
      add_le_add hav hqc
    _ = 4 * E^2 := by ring

/-- The square of an actual compensated original Wilson local GI minor
is bounded by the square of its explicit volume-uniform envelope. -/
theorem p4Q2MA_originalCompensatedLocalGIMinor_sq_le_four_contrastSq_sq
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    (d e e' z z' p)^2 ≤ (4 * E^2)^2 := by
  have hAbs := p4Q2MA_originalCompensatedLocalGIMinor_abs_le_four_contrastSq
    H b hb e e' z z' p
  have hB : 0 ≤ 4 * E^2 := by positivity
  have hProd : 0 ≤
      (4 * E^2 - |d e e' z z' p|) *
      (4 * E^2 + |d e e' z z' p|) :=
    mul_nonneg (sub_nonneg.mpr hAbs)
      (add_nonneg hB (abs_nonneg _))
  have hs : |d e e' z z' p|^2 ≤ (4 * E^2)^2 := by
    nlinarith [hProd]
  simpa only [sq_abs] using hs

/-- The ENTIRE original interacting-Wilson finite-plaquette local GI
square energy is bounded by the actual genuine plaquette count
times a universal-in-H amplitude, without artificial rank or source. -/
theorem p4Q2MA_originalCompensatedLocalGISquareEnergy_le_count_mul
    (e e' : Link) (z z' : Cfg × Cfg) :
    Q e e' z z' ≤ n * (4 * E^2)^2 := by
  classical
  have hFinite := Finset.sum_le_card_nsmul (Finset.univ : Finset Plaq)
    (fun p : Plaq => (d e e' z z' p)^2) ((4 * E^2)^2)
    (fun p hp =>
      p4Q2MA_originalCompensatedLocalGIMinor_sq_le_four_contrastSq_sq
        H b hb e e' z z' p)
  have hCard : n = (Fintype.card Plaq : ℝ) := by
    exact_mod_cast p4Q2LQ_originalSpatialPlaquetteCount_eq_card H
  simpa only [p4Q2LY_originalCompensatedLocalGISquareEnergy,
    hCard, Finset.card_univ, nsmul_eq_mul] using hFinite

/-- True spatial GI square energy PER ACTUAL ORIGINAL PLAQUETTE
has upper bound 16 E_b^4 independent of H, links or contexts. -/
theorem p4Q2MA_originalCompensatedLocalGISquareEnergy_density_le_sixteen
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg) :
    Q e e' z z' / n ≤ 16 * E^4 := by
  have hTotal := p4Q2MA_originalCompensatedLocalGISquareEnergy_le_count_mul
    H b hb e e' z z'
  have hMean : Q e e' z z' / n ≤ (4 * E^2)^2 :=
    (div_le_iff₀ hcount).2 (by simpa only [mul_comm] using hTotal)
  calc
    Q e e' z z' / n ≤ (4 * E^2)^2 := hMean
    _ = 16 * E^4 := by ring

/-- LZ's original spatial plaquette GI local-minor variance has a
genuine volume-uniform UPPER bound. Positivity is not inferred. -/
theorem p4Q2MA_originalCompensatedLocalGIVariance_le_sixteen
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg) :
    V e e' z z' ≤ 16 * E^4 := by
  have hEq :=
    p4Q2LZ_originalCompensatedLocalSquareEnergy_eq_meanSq_add_variance
      H b hb hcount e e' z z'
  have hV : V e e' z z' ≤ Q e e' z z' / n := by
    rw [hEq]
    nlinarith [sq_nonneg (m e e' z z')]
  exact hV.trans
    (p4Q2MA_originalCompensatedLocalGISquareEnergy_density_le_sixteen
      H b hb hcount e e' z z')

/-- The SAME genuine LP/LY selected physical Wilson local plaquette and
two true interacting posterior contexts enjoy both the strictly positive
finite-H lower-energy witness and volume-independent UPPER moment bounds.
This does NOT assert a uniform positive lower bound across H. -/
theorem p4Q2MA_originalPhysicalLocalGI_exists_boundedMoment_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < n ∧
      0 < Q e e' z z' / n ∧
      Q e e' z z' / n ≤ 16 * E^4 ∧
      0 ≤ V e e' z z' ∧
      V e e' z z' ≤ 16 * E^4 ∧
      0 < kappa e e' z z' p ∧
      ((m e e' z z')^2 + V e e' z z') / (10 * E^2) ≤
        kappa e e' z z' p ∧
      ∀ x y : ℝ,
        kappa e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hQ, hMean, hκ, hFloor, hOld, hBound⟩ :=
    p4Q2LY_originalPhysicalLocalGI_exists_squareEnergy_floor
      H b hb hpos e e' left₀ right₀
  have hPos : 0 < Q e e' z z' / n := div_pos hQ hn
  have hUpper :=
    p4Q2MA_originalCompensatedLocalGISquareEnergy_density_le_sixteen
      H b hb hn e e' z z'
  have hVarNonneg :=
    p4Q2LZ_originalCompensatedLocalGIVariance_nonneg
      H b hb hn e e' z z'
  have hVarUpper :=
    p4Q2MA_originalCompensatedLocalGIVariance_le_sixteen
      H b hb hn e e' z z'
  have hDecompose :=
    p4Q2LZ_originalLocalGI_squareEnergyFloor_eq_meanVarianceFloor
      H b hb hn hpos e e' z z'
  have hPhysical :
      ((m e e' z z')^2 + V e e' z z') / (10 * E^2) ≤
        kappa e e' z z' p := by
    rw [← hDecompose]
    exact hFloor
  exact ⟨z, z', p, hp, hn, hPos, hUpper, hVarNonneg, hVarUpper,
    hκ, hPhysical, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalCompensatedGI_unit_abs_le_contrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalCompensatedGI_local_abs_le_two_contrast
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalCompensatedLocalGIMinor_abs_le_four_contrastSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalCompensatedLocalGIMinor_sq_le_four_contrastSq_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalCompensatedLocalGISquareEnergy_le_count_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalCompensatedLocalGISquareEnergy_density_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalCompensatedLocalGIVariance_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MA_originalPhysicalLocalGI_exists_boundedMoment_floor
