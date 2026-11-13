import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalIdentityBoxExplicitPhysicalNormFloorV5_PZ37ALF
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALG — sharp even-Laplace second moment in the original Wilson theory

ALC's original center-twist measure symmetry gives an exact EVEN
two-boundary pair-Haar Laplace transform, without claiming that the
crossing kernel factorizes. Its earlier elementary exp bound had
quadratic coefficient 1/4. Here a pinned mathlib exponential
quadratic bound and the identity exp(x)*exp(-x)=1 establish the
SHARP universal even-exponential coefficient 1/2:

  1 + x^2/2 <= (exp(x)+exp(-x))/2.

We then apply this scalar estimate directly to the ORIGINAL crossing
weighted, Haar-integrable pair source, with the ALC measure-preserving
symmetrization, yielding

  Lpair_H(beta,t) >= Zcross_H(beta) + t^2/2 * M2pair_H(beta).

For the original full SU(2) Wilson one-slab operator this gives

  ||P_H(beta)|| >= exp(-beta*p_H) *
    (Zcross_H(beta) + beta^2/2 * M2pair_H(beta)).

The independent AHN/ALE/ALF real Haar identity box makes the
correction explicit, positive for beta>0, and twice ALF's quantitative
coefficient, WITHOUT modifying any physical definition.

This is finite-volume mathematics only. It supplies neither the
H22 original negative-region r22 upper bound, an AJA verdict,
H-uniform coercivity, nor a continuum mass gap.
Append-only; no existing file, pin, theorem assumption or root changes.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- Derive 2*x <= exp(x)-exp(-x) on x>=0 using only mathlib's
quadratic exponential bound and multiplicative inverse symmetry.
The key algebra is (1+x+x²/2)² - 2*x*(1+x+x²/2) - 1 = x⁴/4. -/
theorem p4Q2PZ37ALG_exp_sub_exp_neg_ge_two_mul
    (x : ℝ) (hx : 0 ≤ x) :
    2 * x ≤ Real.exp x - Real.exp (-x) := by
  let q : ℝ := 1 + x + x ^ 2 / 2
  let e : ℝ := Real.exp x
  have hq : q ≤ e := Real.quadratic_le_exp_of_nonneg hx
  have hqx : x ≤ q := by
    dsimp [q]
    nlinarith [sq_nonneg x]
  have hcross : 0 ≤ (e - q) * (e + q - 2 * x) :=
    mul_nonneg (sub_nonneg.mpr hq) (by linarith only [hq, hqx])
  have hpoly : 0 ≤ q ^ 2 - 2 * x * q - 1 := by
    dsimp [q]
    nlinarith only [sq_nonneg (x ^ 2)]
  have hquad : 0 ≤ e ^ 2 - 2 * x * e - 1 := by
    nlinarith only [hcross, hpoly]
  have hinv : e * Real.exp (-x) = 1 := by
    dsimp [e]
    rw [← Real.exp_add]
    simp
  have hscaled :
      (2 * x) * e ≤ (e - Real.exp (-x)) * e := by
    nlinarith only [hquad, hinv]
  exact (mul_le_mul_iff_of_pos_right (Real.exp_pos x)).mp hscaled

/-- The optimal universal even-exp quadratic estimate.
It improves ALC's 1/4 to 1/2 using pinned mathlib,
not a numerical or Gaussian approximation. -/
theorem p4Q2PZ37ALG_real_expSymm_ge_halfQuadratic (x : ℝ) :
    1 + x ^ 2 / 2 ≤ (Real.exp x + Real.exp (-x)) / 2 := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) :
      1 + y ^ 2 / 2 ≤ (Real.exp y + Real.exp (-y)) / 2 := by
    have hy2 : 0 ≤ y / 2 := by linarith only [hy]
    have hd0 :=
      p4Q2PZ37ALG_exp_sub_exp_neg_ge_two_mul (y / 2) hy2
    have hd : y ≤ Real.exp (y / 2) - Real.exp (-(y / 2)) := by
      convert hd0 using 1 <;> ring
    have hnonnegDiff :
        0 ≤ Real.exp (y / 2) - Real.exp (-(y / 2)) :=
      hy.trans hd
    have hsq :
        0 ≤
          ((Real.exp (y / 2) - Real.exp (-(y / 2))) - y) *
          ((Real.exp (y / 2) - Real.exp (-(y / 2))) + y) :=
      mul_nonneg (sub_nonneg.mpr hd) (by linarith only [hy, hnonnegDiff])
    have hleft :
        Real.exp (y / 2) ^ 2 = Real.exp y := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hright :
        Real.exp (-(y / 2)) ^ 2 = Real.exp (-y) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hprod :
        Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith only [hsq, hleft, hright, hprod]
  rcases le_total 0 x with hx | hx
  · exact hnonneg x hx
  · have h := hnonneg (-x) (by linarith only [hx])
    simpa only [neg_sq, neg_neg, add_comm] using h

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALG_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALG_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALG_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALG_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALG_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "pairH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "KC" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "Lpair" => p4Q2PZ37ALB_originalPairCrossingLaplace H
local notation "M2pair" => p4Q2PZ37ALC_originalPairCrossingSecondMoment H
local notation "kFloor" => p4Q2PZ37ALE_originalCrossingKernelFloor H
local notation "vBox" => p4Q2PZ37ALF_originalIdentityBoxVarianceFloor H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "PW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)

/-- Sharper original two-boundary even Laplace bound. The even
symmetrization is precisely the already-certified ALA/ALB original
diagonal-center, measure-preserving symmetry; it is NOT an assumed
independent crossing action or alternate probability measure. -/
theorem p4Q2PZ37ALG_originalPairLaplace_ge_sharpSecondMoment
    (beta t : ℝ) :
    Zcross beta + (t ^ 2 / 2) * M2pair beta ≤ Lpair beta t := by
  have hKCInt := p4Q2PZ37AIV_originalCrossingKernel_pair_integrable H beta
  have hM2Int :=
    p4Q2PZ37ALC_originalPairCrossingSecondMoment_integrable H beta
  have hPlus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta t
  have hMinus := p4Q2PZ37ALB_originalPairLaplace_integrable H beta (-t)
  have hLowerInt :
      Integrable (fun P : Cfg × Cfg =>
        KC beta P.1 P.2 +
          (t ^ 2 / 2) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2)) pairH :=
    hKCInt.add (hM2Int.const_mul (t ^ 2 / 2))
  have hSymInt :
      Integrable (fun P : Cfg × Cfg =>
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2)) pairH := by
    have hI := (hPlus.add hMinus).const_mul (1 / 2 : ℝ)
    convert hI using 1
    ext P
    dsimp only [Pi.add_apply]
    ring
  have hPointwise (P : Cfg × Cfg) :
      KC beta P.1 P.2 +
          (t ^ 2 / 2) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) ≤
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) := by
    let s : ℝ := fCont P.1 + fCont P.2
    have hKC : 0 ≤ KC beta P.1 P.2 :=
      (p4Q2PZ37AIN_originalCrossingKernel_pos H beta P.1 P.2).le
    have hExp :
        1 + (t * s) ^ 2 / 2 ≤
          (Real.exp (t * s) + Real.exp ((-t) * s)) / 2 := by
      simpa only [neg_mul] using
        p4Q2PZ37ALG_real_expSymm_ge_halfQuadratic (t * s)
    calc
      _ = KC beta P.1 P.2 * (1 + (t * s) ^ 2 / 2) := by
        dsimp [s]
        ring
      _ ≤ KC beta P.1 P.2 *
          ((Real.exp (t * s) + Real.exp ((-t) * s)) / 2) :=
        mul_le_mul_of_nonneg_left hExp hKC
      _ = _ := by rfl
  have hLowerValue :
      (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 +
          (t ^ 2 / 2) *
            (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) ∂pairH) =
      Zcross beta + (t ^ 2 / 2) * M2pair beta := by
    rw [integral_add hKCInt (hM2Int.const_mul (t ^ 2 / 2)),
      integral_const_mul,
      p4Q2PZ37AIV_originalCrossingKernel_pair_integral H beta]
    rfl
  calc
    Zcross beta + (t ^ 2 / 2) * M2pair beta =
        (∫ P : Cfg × Cfg,
          KC beta P.1 P.2 +
            (t ^ 2 / 2) *
              (KC beta P.1 P.2 * (fCont P.1 + fCont P.2) ^ 2) ∂pairH) :=
        hLowerValue.symm
    _ ≤ (∫ P : Cfg × Cfg,
        KC beta P.1 P.2 *
          ((Real.exp (t * (fCont P.1 + fCont P.2)) +
            Real.exp (-t * (fCont P.1 + fCont P.2))) / 2) ∂pairH) :=
      integral_mono hLowerInt hSymInt hPointwise
    _ = Lpair beta t :=
      (p4Q2PZ37ALB_originalPairLaplace_symmetrized H beta t).symm

/-- The true original full one-slab SU(2) Wilson transfer norm gets
the sharp positive second-moment coefficient 1/2, not 1/4. -/
theorem p4Q2PZ37ALG_originalPhysicalNorm_ge_sharpSecondMoment
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta + (beta ^ 2 / 2) * M2pair beta) ≤
        ‖PW beta hbeta‖ := by
  have hLaplace :=
    p4Q2PZ37ALG_originalPairLaplace_ge_sharpSecondMoment H beta (-beta)
  have hScale :=
    mul_le_mul_of_nonneg_left hLaplace (Real.exp_pos (-(beta * pH))).le
  have hPhysical :=
    p4Q2PZ37ALD_originalPhysicalTransfer_norm_ge_pairLaplace
      H beta hbeta
  simpa only [neg_sq] using hScale.trans hPhysical

/-- Inserting independently verified genuine SU(2) Haar identity-box
mass gives twice the previous ALF numerical-coefficient correction,
not an equality with the physical operator norm. -/
theorem p4Q2PZ37ALG_originalPhysicalNorm_ge_sharpIdentityBox
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta + (beta ^ 2 / 2) * (2 * kFloor beta * vBox)) ≤
      ‖PW beta hbeta‖ := by
  have hMoment :=
    p4Q2PZ37ALF_originalPairSecondMoment_ge_identityBoxFloor
      H beta hbeta
  have hScaled :=
    mul_le_mul_of_nonneg_left hMoment
      (show 0 ≤ (beta ^ 2 / 2 : ℝ) by positivity)
  have hInner :
      Zcross beta + (beta ^ 2 / 2) * (2 * kFloor beta * vBox) ≤
      Zcross beta + (beta ^ 2 / 2) * M2pair beta := by
    linarith only [hScaled]
  exact (mul_le_mul_of_nonneg_left hInner
    (Real.exp_pos (-(beta * pH))).le).trans
      (p4Q2PZ37ALG_originalPhysicalNorm_ge_sharpSecondMoment
        H beta hbeta)

/-- At every strictly positive original coupling, the strengthened
certified floor is strictly above ALF's old floor, and both bound the
exact same original physical transfer norm. -/
theorem p4Q2PZ37ALG_originalPhysicalNorm_strictly_gt_ALF_boxFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    Real.exp (-(beta * pH)) *
      (Zcross beta + (beta ^ 2 / 4) * (2 * kFloor beta * vBox)) <
      ‖PW beta hbeta.le‖ := by
  have hKF := p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hBox := p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  have hCorr :
      0 < (beta ^ 2 / 4) * (2 * kFloor beta * vBox) := by
    have hβ : 0 < (beta ^ 2 / 4 : ℝ) := by positivity
    exact mul_pos hβ (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hKF) hBox)
  have hInner :
      Zcross beta + (beta ^ 2 / 4) * (2 * kFloor beta * vBox) <
      Zcross beta + (beta ^ 2 / 2) * (2 * kFloor beta * vBox) := by
    nlinarith only [hCorr]
  have hScale :=
    mul_lt_mul_of_pos_left hInner (Real.exp_pos (-(beta * pH)))
  exact hScale.trans_le
    (p4Q2PZ37ALG_originalPhysicalNorm_ge_sharpIdentityBox
      H beta hbeta.le)

/-- True H=22 fixed beta0 with exact original p22=292008, unchanged
physical source, Haar, halfweights, crossing and full transfer. -/
theorem p4Q2PZ37ALG_originalH22_fixedCoupling_physicalNorm_sharpBox :
    Real.exp (-(p4Q2PZ37ADC_fixedCoupling * (292008 : ℝ))) *
      (p4Q2PZ37AIF_originalCrossingPartition 22
          p4Q2PZ37ADC_fixedCoupling +
        (p4Q2PZ37ADC_fixedCoupling ^ 2 / 2) *
          (2 * p4Q2PZ37ALE_originalCrossingKernelFloor 22
            p4Q2PZ37ADC_fixedCoupling *
            p4Q2PZ37ALF_originalIdentityBoxVarianceFloor 22)) ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          22 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
            p4Q2PZ37ADC_fixedCoupling_pos.le‖ := by
  have h :=
    p4Q2PZ37ALG_originalPhysicalNorm_ge_sharpIdentityBox
      22 p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ALG_exp_sub_exp_neg_ge_two_mul
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ALG_real_expSymm_ge_halfQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALG_originalPairLaplace_ge_sharpSecondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALG_originalPhysicalNorm_ge_sharpSecondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALG_originalPhysicalNorm_ge_sharpIdentityBox
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALG_originalPhysicalNorm_strictly_gt_ALF_boxFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALG_originalH22_fixedCoupling_physicalNorm_sharpBox
