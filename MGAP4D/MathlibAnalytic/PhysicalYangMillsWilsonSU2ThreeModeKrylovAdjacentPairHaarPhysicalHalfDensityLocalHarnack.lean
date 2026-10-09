import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHalfDensityMeanLinkBudget
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack
import Mathlib.Tactic

/-!
# P4-Q2-A: genuine joint half-density right-link Harnack estimate

For the exact finite-volume Wilson joint half-density

  W(A,B) = ‖T_beta‖⁻¹ * Omega_beta(B) /
    sqrt(‖T_beta‖⁻¹ * Omega_beta(A) * K_beta(A,B) * Omega_beta(B)),

the volume-uniform one-link comparison of the positive continuous vacuum
and the reverse comparison of the TRUE one-slab kernel together imply

  W(A,B[e <- g]) <= exp(8*beta) * W(A,B).

Using the reverse update gives an actual signed variation estimate

  |W(A,B[e <- g]) - W(A,B)|
      <= (exp(8*beta)-1) * ‖W‖.

The local multiplicative coefficient has no link-count or finite-volume
dependence; the BCF norm ‖W‖ itself may depend on volume. This is not
an unproved finite-range posterior hypothesis. The signed physical
transfer mean is not replaced, and no claim about volume-uniform Gram
operator norms or continuum mass gap is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4HalfHarnackTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4HalfHarnackCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4HalfHarnackSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4HalfHarnackMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4HalfHarnackBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4HalfHarnackLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A positive algebraic half-density comparison. It deliberately uses
a comparison of the numerator and the OPPOSITE comparison of the
positive kernel; no signed integral is compared by positivity. -/
private theorem positive_halfDensity_mul_sqrt_le
    (l x y y' k k' R : ℝ)
    (hl : 0 < l) (hx : 0 < x)
    (hy : 0 < y) (hy' : 0 < y')
    (hk : 0 < k) (hk' : 0 < k')
    (hR : 0 < R)
    (hY : y' ≤ R * y) (hK : k ≤ R * k') :
    (l * y') / Real.sqrt (l * (x * k' * y')) ≤
      R * ((l * y) / Real.sqrt (l * (x * k * y))) := by
  let q := l * (x * k * y)
  let q' := l * (x * k' * y')
  let w := (l * y) / Real.sqrt q
  let w' := (l * y') / Real.sqrt q'
  change w' ≤ R * w
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : 0 < q' := by dsimp [q']; positivity
  have hwsq : w ^ 2 * (x * k) = l * y := by
    dsimp [w]
    rw [div_pow, Real.sq_sqrt hq.le]
    dsimp [q]
    field_simp [ne_of_gt hl, ne_of_gt hx, ne_of_gt hk, ne_of_gt hy]
    <;> ring
  have hwsq' : w' ^ 2 * (x * k') = l * y' := by
    dsimp [w']
    rw [div_pow, Real.sq_sqrt hq'.le]
    dsimp [q']
    field_simp [ne_of_gt hl, ne_of_gt hx, ne_of_gt hk', ne_of_gt hy']
    <;> ring
  have hYscale : l * y' ≤ R * (l * y) := by
    calc
      l * y' ≤ l * (R * y) := mul_le_mul_of_nonneg_left hY hl.le
      _ = R * (l * y) := by ring
  have hKscale : x * k ≤ x * (R * k') :=
    mul_le_mul_of_nonneg_left hK hx.le
  have hProduct : w ^ 2 * (x * k) ≤ w ^ 2 * (x * (R * k')) :=
    mul_le_mul_of_nonneg_left hKscale (sq_nonneg w)
  have hSquared : w' ^ 2 * (x * k') ≤ (R * w) ^ 2 * (x * k') := by
    calc
      w' ^ 2 * (x * k') = l * y' := hwsq'
      _ ≤ R * (l * y) := hYscale
      _ = R * (w ^ 2 * (x * k)) := by rw [hwsq]
      _ ≤ R * (w ^ 2 * (x * (R * k'))) :=
        mul_le_mul_of_nonneg_left hProduct hR.le
      _ = (R * w) ^ 2 * (x * k') := by ring
  have hSq : w' ^ 2 ≤ (R * w) ^ 2 :=
    (mul_le_mul_right (mul_pos hx hk')).mp hSquared
  have hw : 0 ≤ w := by
    change 0 ≤ (l * y) / Real.sqrt q
    exact div_nonneg (mul_nonneg hl.le hy.le) (Real.sqrt_nonneg q)
  have hw' : 0 ≤ w' := by
    change 0 ≤ (l * y') / Real.sqrt q'
    exact div_nonneg (mul_nonneg hl.le hy'.le) (Real.sqrt_nonneg q')
  have hRw : 0 ≤ R * w := mul_nonneg hR.le hw
  nlinarith

/-- The ACTUAL finite-volume Wilson half-density has a right-link
Harnack coefficient exp(8*beta), independent of lattice size.
The physical vacuum and the full Wilson one-slab kernel are retained,
including the exact ground-state joint square-root density. -/
theorem normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
        (z.1, Function.update z.2 e g) ≤
      Real.exp (8 * beta) *
        normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z := by
  classical
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let R := Real.exp (8 * beta)
  let B' := Function.update z.2 e g
  have hl : 0 < l :=
    inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)
  have hx : 0 < Omega z.1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.1
  have hy : 0 < Omega z.2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta z.2
  have hy' : 0 < Omega B' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B'
  have hk : 0 < K z.1 z.2 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta z.1 z.2
  have hk' : 0 < K z.1 B' :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta z.1 B'
  have hR : 0 < R := Real.exp_pos _
  have hOmega : Omega B' ≤ R * Omega z.2 := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta z.2 e g (z.2 e)
    simpa [Omega, R, B',
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using h
  have hKernel : K z.1 z.2 ≤ R * K z.1 B' := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta z.1 z.2 e (z.2 e) g
    simpa [K, R, B',
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using h
  change (l * Omega B') /
      Real.sqrt (l * (Omega z.1 * K z.1 B' * Omega B')) ≤
    R * ((l * Omega z.2) /
      Real.sqrt (l * (Omega z.1 * K z.1 z.2 * Omega z.2)))
  exact positive_halfDensity_mul_sqrt_le
    l (Omega z.1) (Omega z.2) (Omega B') (K z.1 z.2) (K z.1 B') R
    hl hx hy hy' hk hk' hR hOmega hKernel

/-- Genuine signed one-link oscillation of the SAME original Wilson
half-density, controlled by a coefficient independent of the number of
links. The unavoidable global BCF norm remains explicit. -/
theorem normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightLinkDifference_abs_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta z -
      normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
        (z.1, Function.update z.2 e g)| ≤
      (Real.exp (8 * beta) - 1) *
        ‖normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta‖ := by
  classical
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let R := Real.exp (8 * beta)
  let z' := (z.1, Function.update z.2 e g)
  have hR : 1 ≤ R := by
    change Real.exp 0 ≤ Real.exp (8 * beta)
    exact Real.exp_le_exp.mpr (by nlinarith [hbeta])
  have hForward : W z' ≤ R * W z :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
      H N hN beta hbeta e z g
  have hRest :
      Function.update (Function.update z.2 e g) e (z.2 e) = z.2 := by
    simp
  have hBackward : W z ≤ R * W z' := by
    have h :=
      normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
        H N hN beta hbeta e z' (z.2 e)
    simpa only [hRest] using h
  have hOld : W z ≤ ‖W‖ := by
    calc
      W z ≤ |W z| := le_abs_self _
      _ ≤ ‖W‖ := by simpa only [Real.norm_eq_abs] using W.norm_coe_le_norm z
  have hNew : W z' ≤ ‖W‖ := by
    calc
      W z' ≤ |W z'| := le_abs_self _
      _ ≤ ‖W‖ := by simpa only [Real.norm_eq_abs] using W.norm_coe_le_norm z'
  have hRminus : 0 ≤ R - 1 := by linarith
  have hForwardDiff : W z' - W z ≤ (R - 1) * ‖W‖ := by
    calc
      W z' - W z ≤ (R - 1) * W z := by nlinarith [hForward]
      _ ≤ (R - 1) * ‖W‖ := mul_le_mul_of_nonneg_left hOld hRminus
  have hBackwardDiff : W z - W z' ≤ (R - 1) * ‖W‖ := by
    calc
      W z - W z' ≤ (R - 1) * W z' := by nlinarith [hBackward]
      _ ≤ (R - 1) * ‖W‖ := mul_le_mul_of_nonneg_left hNew hRminus
  exact abs_le.mpr ⟨by linarith, hBackwardDiff⟩

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
