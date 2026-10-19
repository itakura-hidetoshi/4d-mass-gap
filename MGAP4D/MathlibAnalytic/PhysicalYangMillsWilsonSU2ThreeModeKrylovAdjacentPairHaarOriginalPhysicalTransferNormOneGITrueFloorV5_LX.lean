import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferNormalizationCompensatedCoercivityV5_LW
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabHaarL2Transfer
import Mathlib.Tactic

/-!
# P4-Q2-LX — original SU(2) physical transfer norm ≤ 1 and direct physical GI floor

LW proves genuine transfer-compensated original Wilson GI coercivity:
  κbar_p=||T||² κ_p ≥ Δbar_total²/(10 N_H² E_b²)
with E_b=exp(8b)(exp(16b)-exp(-16b)).

The original complete Wilson one-slab kernel satisfies |K|≤1 pointwise,
for ALL H at b≥0. Its actual two-boundary Haar measure is a probability
measure. The PINNED mathlib Lp.norm_le_of_ae_bound thus yields
  ||K||_{Haar²,L²}≤1.
The ACTUAL Hilbert–Schmidt integral transfer and its Gauss-law physical
restriction have operator norms bounded by that very same original kernel
L² norm, using the ALREADY PROVED physical/ambient factorization.

Thus, WITHOUT any extra hypothesis on rank, posterior or physical source:
  0<||T_{H,b}||≤1   and   0<||T_{H,b}||²≤1.
In particular the true original κ_p dominates the compensated κbar_p,
because κbar_p=||T||² κ_p and κ_p>0 at the proved original GI minor.

We obtain a stronger ORIGINAL PHYSICAL (uncompensated) finite-H bound:
  κ_p ≥ Δbar_total²/(10 N_H² E_b²)
on the exact original Gauss-law two-source plane at the SAME genuine
two-context LP-selected Wilson plaquette. No factor ||T|| or ||T||⁻¹
remains explicitly on the lower-bound DENOMINATOR.

Importantly Δbar_total=||T||² Δ_total is a TRUE rescaled original Wilson
minor, still H-dependent. Neither Δbar_total/N_H nor physical κ_p
is known to have a uniform positive lower bound. This does not prove
H1-C3, continuum Yang–Mills or the mass gap.

No independent Haar posterior replacement (Haar is only the genuine
original reference measure), Dobrushin, synthetic detector, source,
rank hypothesis, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "pairHaar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "tN" => p4Q2LW_originalPhysicalTransferNorm H b hb
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "kPair" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
    H 2 (by norm_num) b hb

/-- The unchanged true interacting SU(2) Wilson Boltzmann kernel, in
its existing pair-Haar L² representation, has norm ≤1 on the
ORIGINAL product probability Haar measure for every finite volume H. -/
theorem p4Q2LX_originalWilsonPairHaarL2Kernel_norm_le_one :
    ‖kPair‖ ≤ (1 : ℝ) := by
  let μ := pairHaar
  let k : Lp ℝ 2 μ := kPair
  have hAE : ∀ᵐ z ∂μ, ‖k z‖ ≤ (1 : ℝ) := by
    filter_upwards
      [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H 2 (by norm_num) b hb] with z hz
    rw [hz, Real.norm_eq_abs]
    exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      H 2 (by norm_num) b hb z.1 z.2
  have hLp := MeasureTheory.Lp.norm_le_of_ae_bound
    (f := k) (C := (1 : ℝ)) (by norm_num) hAE
  simpa [μ, measureUnivNNReal] using hLp

/-- Genuine physical one-slab transfer (Gauss-law restriction) has
operator norm bounded by ONE, uniformly in finite lattice volume.
The proof traverses actual HS kernel and ambient integral operator. -/
theorem p4Q2LX_originalPhysicalTransferNorm_le_one :
    tN ≤ 1 := by
  change ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b hb‖ ≤ 1
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b hb‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H 2 (by norm_num) b hb‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_le_ambient
        H 2 (by norm_num) b hb
    _ ≤ ‖kPair‖ :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_le
        H 2 (by norm_num) b hb
    _ ≤ 1 := p4Q2LX_originalWilsonPairHaarL2Kernel_norm_le_one H b hb

/-- True transfer-norm square is positive and at most one. This
uses the EXISTING JH/physical vacuum norm-positivity theorem. -/
theorem p4Q2LX_originalPhysicalTransferNorm_sq_pos_le_one :
    0 < tN^2 ∧ tN^2 ≤ 1 := by
  have ht := p4Q2LW_originalPhysicalTransferNorm_pos H b hb
  have hle := p4Q2LX_originalPhysicalTransferNorm_le_one H b hb
  constructor
  · exact sq_pos_of_pos ht
  · have hprod : 0 ≤ (1 - tN) * (1 + tN) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) ht.le)
    nlinarith [hprod]

/-- IMPORTANT: For the SAME actual original physical local GI minor,
LW's scalar-compensated κbar is ≤ the TRUE physical κ, because
0<||T||²≤1. No comparison of different physical sources is made. -/
theorem p4Q2LX_originalCompensatedLocalGICoefficient_le_truePhysical
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq)
    (hminor : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0) :
    p4Q2LW_originalCompensatedLocalGICoefficient H b hb e e' z z' p ≤
      p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb e e' z z' p := by
  let κ := p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb e e' z z' p
  have hκ : 0 < κ :=
    (p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hminor).1
  have htSq : tN^2 ≤ 1 :=
    (p4Q2LX_originalPhysicalTransferNorm_sq_pos_le_one H b hb).2
  rw [p4Q2LW_originalCompensatedLocalGICoefficient_eq_sq_mul_original
    H b hb e e' z z' p hminor]
  change tN^2 * κ ≤ κ
  calc
    tN^2 * κ ≤ 1 * κ :=
      mul_le_mul_of_nonneg_right htSq hκ.le
    _ = κ := one_mul _

/-- The actual ORIGINAL (not compensated) Gauss-law physical local GI
coercivity coefficient now has an explicit finite-H lower bound free of
ALL pointwise half-density and transfer-normalization denominator loss:
  κ_p ≥ Δbar_total²/(10 N_H² E_b²).
Only the genuine compensated total determinant and count remain. -/
theorem p4Q2LX_originalPhysicalLocalGI_ge_compensatedGlobal_floor
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
      p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb e e' z z' p := by
  exact (p4Q2LW_originalCompensatedLocalGI_ge_compensatedGlobal_floor
    H b hb hpos e e' z z' p hminor hcount hAvg).trans
      (p4Q2LX_originalCompensatedLocalGICoefficient_le_truePhysical
        H b hb e e' z z' p hminor)

/-- Strongest currently proved ORIGINAL finite-H SU(2) physical
two-source GI certificate. The selected p and contexts are still the
unchanged original Wilson LP witnesses. The missing analytic input for
volume-uniform coercivity is a positive lower bound for the ORIGINAL
transfer-compensated GI determinant divided by actual plaquette count. -/
theorem p4Q2LX_originalPhysicalLocalGI_exists_true_floor
    (hpos : 0 < b) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < p4Q2LO_originalLocalGIQuantitativeCoefficient
        H b hb e e' z z' p ∧
      (p4Q2LW_originalCompensatedSpatialGIMinor H b hb e e' z z')^2 /
        ((p4Q2LP_originalSpatialPlaquetteCount H : ℝ)^2 *
          (10 * E^2)) ≤
        p4Q2LO_originalLocalGIQuantitativeCoefficient H b hb e e' z z' p ∧
      ∀ x y : ℝ,
        p4Q2LO_originalLocalGIQuantitativeCoefficient
          H b hb e e' z z' p * (x^2 + y^2) ≤
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
          (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b hb (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hpos e e' left₀ right₀
  have hlocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  obtain ⟨hκ, hBound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb e e' z z' p hlocal
  have hFloor := p4Q2LX_originalPhysicalLocalGI_ge_compensatedGlobal_floor
    H b hb hpos e e' z z' p hlocal hn hAvg
  exact ⟨z, z', p, hp, hn, hκ, hFloor, hBound⟩

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LX_originalWilsonPairHaarL2Kernel_norm_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LX_originalPhysicalTransferNorm_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LX_originalPhysicalTransferNorm_sq_pos_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LX_originalCompensatedLocalGICoefficient_le_truePhysical
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LX_originalPhysicalLocalGI_ge_compensatedGlobal_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LX_originalPhysicalLocalGI_exists_true_floor
