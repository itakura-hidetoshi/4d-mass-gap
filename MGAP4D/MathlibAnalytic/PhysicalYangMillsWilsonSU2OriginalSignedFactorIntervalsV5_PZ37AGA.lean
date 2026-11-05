import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRationalReceiverEnvelopeV5_PZ37AFZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGA — signed rational factor intervals for the ORIGINAL FF receiver

AFZ constructed the unconditional but conservative zero-midpoint rational
interval for the original FF/Perron/transfer physical receiver. AGA adds a
STRICTLY ADDITIVE alternative: rational interval arithmetic on the actual
physical factors of the original, exact AFZ receiver identity

  F_e(z,g) = a * (u - r*v),
  a = ‖T_H‖⁻¹, u = t_H(B), r = rho_H(z)/rho_H(z_g), v = t_H(B_g).

Each input is an AFV verified interval containing the actual original
real quantity. AGA derives a rational midpoint qF and a rational
half-width EF, with |F_e(z,g) - qF| <= EF. The signed midpoint is
NOT replaced by AFZ's zero. Strict comparisons qF > EF and
qF < -EF are sufficient for genuine original physical receiver signs.

We construct both (1) a full high-precision factor interface, and (2)
a transfer-only interface that DISCHARGES the inverse norm and density
ratio intervals automatically with the unconditional AFZ bounds.
The latter is conservative and is NOT claimed to prove nonzero signs.
Both interfaces feed exactly the existing AFW -> AFX -> AFV -> AFT/AFI
physical receiver certificates at AFQ's true 24 SU(2) centers.

No independently certified nonzero transfer integral, Perron sample,
two-sign shell, volume-uniform coercivity, Hamiltonian spectral gap or
continuum 4D Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Explicit rational center AND rational error, both with Lean inclusion
evidence for the unchanged true real value. -/
structure p4Q2PZ37AGA_rationalBall (x : ℝ) where
  sample : ℚ
  radius : ℚ
  radius_nonneg : 0 ≤ radius
  hContains : |x - (sample : ℝ)| ≤ (radius : ℝ)

/-- Convert an AFV rational endpoint inclusion into rational midpoint/radius. -/
def p4Q2PZ37AGA_fromVerifiedInterval {x : ℝ}
    (v : p4Q2PZ37AFV_verifiedInterval x) :
    p4Q2PZ37AGA_rationalBall x where
  sample := (v.lower + v.upper) / 2
  radius := (v.upper - v.lower) / 2
  radius_nonneg := by
    exact div_nonneg (sub_nonneg.mpr (p4Q2PZ37AFV_interval_ordered v))
      (by norm_num)
  hContains := by
    have h := (p4Q2PZ37AFV_intervalToBall v).hContains
    change |x - ((((v.lower + v.upper) / 2 : ℚ) : ℝ))| ≤
      (((v.upper - v.lower : ℚ) : ℝ) / 2) at h
    convert h using 1 <;> push_cast <;> ring

/-- Forget the rational-error refinement to the pre-existing AFV ball. -/
def p4Q2PZ37AGA_toAFVBall {x : ℝ}
    (b : p4Q2PZ37AGA_rationalBall x) :
    p4Q2PZ37AFV_certifiedBall x where
  sample := b.sample
  error := (b.radius : ℝ)
  error_nonneg := by exact_mod_cast b.radius_nonneg
  hContains := b.hContains

/-- Rational subtraction with no unverified uncertainty cancellation. -/
def p4Q2PZ37AGA_rationalBall_sub {x y : ℝ}
    (bx : p4Q2PZ37AGA_rationalBall x)
    (byy : p4Q2PZ37AGA_rationalBall y) :
    p4Q2PZ37AGA_rationalBall (x - y) where
  sample := bx.sample - byy.sample
  radius := bx.radius + byy.radius
  radius_nonneg := add_nonneg bx.radius_nonneg byy.radius_nonneg
  hContains := by
    calc
      |(x - y) - (((bx.sample - byy.sample : ℚ) : ℝ))| =
          |(x - (bx.sample : ℝ)) - (y - (byy.sample : ℝ))| := by
            push_cast
            congr 1
            ring
      _ ≤ |x - (bx.sample : ℝ)| + |y - (byy.sample : ℝ)| :=
        abs_sub_le _ _
      _ ≤ (bx.radius : ℝ) + (byy.radius : ℝ) :=
        add_le_add bx.hContains byy.hContains
      _ = (((bx.radius + byy.radius : ℚ) : ℝ)) := by push_cast; ring

/-- Rational multiplication, specializing the already proved AFV
real enclosure and retaining an EXACT rational error. -/
def p4Q2PZ37AGA_rationalBall_mul {x y : ℝ}
    (bx : p4Q2PZ37AGA_rationalBall x)
    (byy : p4Q2PZ37AGA_rationalBall y) :
    p4Q2PZ37AGA_rationalBall (x * y) where
  sample := bx.sample * byy.sample
  radius := bx.radius * (|byy.sample| + byy.radius) +
    |bx.sample| * byy.radius
  radius_nonneg := by
    apply add_nonneg
    · exact mul_nonneg bx.radius_nonneg
        (add_nonneg (abs_nonneg _) byy.radius_nonneg)
    · exact mul_nonneg (abs_nonneg _) byy.radius_nonneg
  hContains := by
    have h := (p4Q2PZ37AFV_ballMul
      (p4Q2PZ37AGA_toAFVBall bx)
      (p4Q2PZ37AGA_toAFVBall byy)).hContains
    change |x * y - (((bx.sample * byy.sample : ℚ) : ℝ))| ≤
      (bx.radius : ℝ) * (|(byy.sample : ℝ)| + (byy.radius : ℝ)) +
      |(bx.sample : ℝ)| * (byy.radius : ℝ) at h
    convert h using 1 <;> push_cast <;> ring

/-- Turn any rational ball into a typed AFV rational interval. -/
def p4Q2PZ37AGA_toVerifiedInterval {x : ℝ}
    (b : p4Q2PZ37AGA_rationalBall x) :
    p4Q2PZ37AFV_verifiedInterval x where
  lower := b.sample - b.radius
  upper := b.sample + b.radius
  hLower := by
    have h := (abs_le.mp b.hContains).1
    simp only [Rat.cast_sub]
    linarith only [h]
  hUpper := by
    have h := (abs_le.mp b.hContains).2
    simp only [Rat.cast_add]
    linarith only [h]

/-- A rational midpoint strictly outside its error on the POSITIVE
side proves an actual positive real observable, without sign guesses. -/
theorem p4Q2PZ37AGA_rationalBall_positive {x : ℝ}
    (b : p4Q2PZ37AGA_rationalBall x)
    (h : b.radius < b.sample) : 0 < x := by
  have hh : (b.radius : ℝ) < (b.sample : ℝ) := by exact_mod_cast h
  have hlow := (abs_le.mp b.hContains).1
  linarith only [hh, hlow]

theorem p4Q2PZ37AGA_rationalBall_negative {x : ℝ}
    (b : p4Q2PZ37AGA_rationalBall x)
    (h : b.sample < -b.radius) : x < 0 := by
  have hh : (b.sample : ℝ) < -(b.radius : ℝ) := by exact_mod_cast h
  have hupp := (abs_le.mp b.hContains).2
  linarith only [hh, hupp]

/-- Abstract certificate for the exact affine product a*(u-r*v).
All four objects and all four enclosures retain their original values. -/
def p4Q2PZ37AGA_fourFactorBall {a u r v : ℝ}
    (ba : p4Q2PZ37AGA_rationalBall a)
    (bu : p4Q2PZ37AGA_rationalBall u)
    (br : p4Q2PZ37AGA_rationalBall r)
    (bv : p4Q2PZ37AGA_rationalBall v) :
    p4Q2PZ37AGA_rationalBall (a * (u - r * v)) :=
  p4Q2PZ37AGA_rationalBall_mul ba
    (p4Q2PZ37AGA_rationalBall_sub bu
      (p4Q2PZ37AGA_rationalBall_mul br bv))

/-- Unlike AFZ's zero midpoint, the exact arithmetic midpoint is SIGNED. -/
theorem p4Q2PZ37AGA_fourFactor_sample {a u r v : ℝ}
    (ba : p4Q2PZ37AGA_rationalBall a)
    (bu : p4Q2PZ37AGA_rationalBall u)
    (br : p4Q2PZ37AGA_rationalBall r)
    (bv : p4Q2PZ37AGA_rationalBall v) :
    (p4Q2PZ37AGA_fourFactorBall ba bu br bv).sample =
      ba.sample * (bu.sample - br.sample * bv.sample) := rfl

/-- The complete rational error formula, including the cross error
eps_r * eps_v (which must not be silently omitted). -/
theorem p4Q2PZ37AGA_fourFactor_radius {a u r v : ℝ}
    (ba : p4Q2PZ37AGA_rationalBall a)
    (bu : p4Q2PZ37AGA_rationalBall u)
    (br : p4Q2PZ37AGA_rationalBall r)
    (bv : p4Q2PZ37AGA_rationalBall v) :
    (p4Q2PZ37AGA_fourFactorBall ba bu br bv).radius =
      ba.radius *
        (|bu.sample - br.sample * bv.sample| +
          (bu.radius + |br.sample| * bv.radius +
            |bv.sample| * br.radius + br.radius * bv.radius)) +
      |ba.sample| *
        (bu.radius + |br.sample| * bv.radius +
          |bv.sample| * br.radius + br.radius * bv.radius) := by
  change ba.radius * (|bu.sample - br.sample * bv.sample| +
      (bu.radius + (br.radius * (|bv.sample| + bv.radius) +
        |br.sample| * bv.radius))) +
    |ba.sample| * (bu.radius +
      (br.radius * (|bv.sample| + bv.radius) + |br.sample| * bv.radius)) = _
  ring

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0 f0
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "F" =>
  p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0

local instance p4Q2PZ37AGA_links : Fintype Link := Fintype.ofFinite _

/-- Input only rational enclosures for the four ACTUAL physical FF
constituents, never a postulated interval for F itself. -/
structure p4Q2PZ37AGA_originalFactorIntervals
    (e : Link) (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  inverseNorm : p4Q2PZ37AFV_verifiedInterval (Tnorm⁻¹)
  unupdatedTransfer : (z : Pair) → z ∈ c.s →
    p4Q2PZ37AFV_verifiedInterval (t z.2)
  densityRatio : (z : Pair) → z ∈ c.s →
    (i : Fin (Fintype.card Grid)) →
      p4Q2PZ37AFV_verifiedInterval
        (rho z / rho (z.1, Function.update z.2 e (gridCenter i)))
  updatedTransfer : (z : Pair) → z ∈ c.s →
    (i : Fin (Fintype.card Grid)) →
      p4Q2PZ37AFV_verifiedInterval
        (t (Function.update z.2 e (gridCenter i)))

/-- Actual original receiver ball at each of the existing AFQ 24 centers.
The original ABZ/AFZ identity is the ONLY factorization step. -/
def p4Q2PZ37AGA_originalCenterBall
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AGA_originalFactorIntervals H e lo hi c)
    (z : Pair) (hz : z ∈ c.s)
    (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AGA_rationalBall (F e z (gridCenter i)) := by
  rw [p4Q2PZ37AFZ_originalFF_eq_densityRatioTransfer]
  exact p4Q2PZ37AGA_fourFactorBall
    (p4Q2PZ37AGA_fromVerifiedInterval d.inverseNorm)
    (p4Q2PZ37AGA_fromVerifiedInterval (d.unupdatedTransfer z hz))
    (p4Q2PZ37AGA_fromVerifiedInterval (d.densityRatio z hz i))
    (p4Q2PZ37AGA_fromVerifiedInterval (d.updatedTransfer z hz i))

/-- Derived actual FF interval: true inclusion is proved from four
physical factor intervals rather than accepted as a fifth input. -/
def p4Q2PZ37AGA_originalCenterInterval
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AGA_originalFactorIntervals H e lo hi c)
    (z : Pair) (hz : z ∈ c.s)
    (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_verifiedInterval (F e z (gridCenter i)) :=
  p4Q2PZ37AGA_toVerifiedInterval
    (p4Q2PZ37AGA_originalCenterBall H e c d z hz i)

/-- Distinguish strict certified sign from merely having a nonzero
rational center; actual physical strict positivity is a theorem. -/
theorem p4Q2PZ37AGA_originalCenter_signPos
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AGA_originalFactorIntervals H e lo hi c)
    (z : Pair) (hz : z ∈ c.s) (i : Fin (Fintype.card Grid))
    (h : (p4Q2PZ37AGA_originalCenterBall H e c d z hz i).radius <
      (p4Q2PZ37AGA_originalCenterBall H e c d z hz i).sample) :
    0 < F e z (gridCenter i) :=
  p4Q2PZ37AGA_rationalBall_positive
    (p4Q2PZ37AGA_originalCenterBall H e c d z hz i) h

theorem p4Q2PZ37AGA_originalCenter_signNeg
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AGA_originalFactorIntervals H e lo hi c)
    (z : Pair) (hz : z ∈ c.s) (i : Fin (Fintype.card Grid))
    (h : (p4Q2PZ37AGA_originalCenterBall H e c d z hz i).sample <
      -(p4Q2PZ37AGA_originalCenterBall H e c d z hz i).radius) :
    F e z (gridCenter i) < 0 :=
  p4Q2PZ37AGA_rationalBall_negative
    (p4Q2PZ37AGA_originalCenterBall H e c d z hz i) h

/-- Transfer the factored signed samples through the UNMODIFIED AFW
receiver-only interface, and hence through AFX's exact characters. -/
def p4Q2PZ37AGA_toOriginalReceiverIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AGA_originalFactorIntervals H e lo hi c) :
    p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c where
  receiver := fun z hz i => p4Q2PZ37AGA_originalCenterInterval H e c d z hz i

noncomputable def p4Q2PZ37AGA_toOriginalCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AGA_originalFactorIntervals H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFX_toOriginalCoefficientVariance H e c hlo
    (p4Q2PZ37AGA_toOriginalReceiverIntervals H e c d)

/-- Unconditional AFZ inverse-norm enclosure: no independent
numerical Perron/transfer norm input is needed in coarse mode. -/
def p4Q2PZ37AGA_automaticInverseNormInterval :
    p4Q2PZ37AFV_verifiedInterval (Tnorm⁻¹) where
  lower := 0
  upper := p4Q2PZ37AFZ_rationalInverseNorm H
  hLower := by
    exact (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) b0 hb0)).le
  hUpper := p4Q2PZ37AFZ_originalInverseNorm_le_rational H

/-- Unconditional AFZ density-ratio bounds for every real SU(2) link. -/
def p4Q2PZ37AGA_automaticDensityRatioInterval
    (e : Link) (z : Pair) (g : G) :
    p4Q2PZ37AFV_verifiedInterval
      (rho z / rho (z.1, Function.update z.2 e g)) where
  lower := 0
  upper := 3 / 2
  hLower := (p4Q2PZ37AFZ_originalDensityRatio_bounds H e z g).1
  hUpper := (p4Q2PZ37AFZ_originalDensityRatio_bounds H e z g).2

/-- The only REMAINING independently verified finite inputs are the
signed ORIGINAL one-slab transfer integrals at the actual boundary
sample and its actual 24 SU(2) link updates. -/
structure p4Q2PZ37AGA_originalTransferOnlyIntervals
    (e : Link) (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  unupdatedTransfer : (z : Pair) → z ∈ c.s →
    p4Q2PZ37AFV_verifiedInterval (t z.2)
  updatedTransfer : (z : Pair) → z ∈ c.s →
    (i : Fin (Fintype.card Grid)) →
      p4Q2PZ37AFV_verifiedInterval
        (t (Function.update z.2 e (gridCenter i)))

/-- Replace only the two NONTRANSFER factor intervals by values proved
unconditionally from the unchanged AFZ genuine Wilson physics. -/
def p4Q2PZ37AGA_transferOnly_toFactorIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AGA_originalTransferOnlyIntervals H e lo hi c) :
    p4Q2PZ37AGA_originalFactorIntervals H e lo hi c where
  inverseNorm := p4Q2PZ37AGA_automaticInverseNormInterval H
  unupdatedTransfer := d.unupdatedTransfer
  densityRatio := fun z _ i =>
    p4Q2PZ37AGA_automaticDensityRatioInterval H e z (gridCenter i)
  updatedTransfer := d.updatedTransfer

/-- Two signed transfer-interval inputs suffice to construct a genuine
FF receiver interval and original four-mode coefficient certificate. -/
noncomputable def p4Q2PZ37AGA_transferOnly_toOriginalCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AGA_originalTransferOnlyIntervals H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AGA_toOriginalCoefficientVariance H e c hlo
    (p4Q2PZ37AGA_transferOnly_toFactorIntervals H e c d)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_fromVerifiedInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_toAFVBall
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_rationalBall_sub
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_rationalBall_mul
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_toVerifiedInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_rationalBall_positive
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_rationalBall_negative
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_fourFactor_sample
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGA_fourFactor_radius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_originalCenterBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_originalCenter_signPos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_originalCenter_signNeg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_toOriginalReceiverIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_toOriginalCoefficientVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_automaticInverseNormInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_automaticDensityRatioInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_transferOnly_toFactorIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGA_transferOnly_toOriginalCoefficientVariance
