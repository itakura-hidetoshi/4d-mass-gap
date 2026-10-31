import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorPositiveHaarRegionV5_PZ37ABV
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABW — actual physical signed receiver on the genuine Haar cap

Retain the original Gauss-law Hilbert physical source, FF signed receiver,
both unchanged interacting posterior densities, and their ABT symmetric
two-copy Haar pairing. ABV supplies the positive-measure region
U = {E(g) ≤ 1/2} × {3/2 ≤ E(h)} and the original determinant floor.

A receiver-difference floor eta >= 0 is an EXPLICIT hypothesis on U,
not a theorem about arbitrary physical sources. It yields a quantitative
restricted signed-pair floor, a lower bound for its global positive part,
and two versions of the original GI gap bound, each requiring a separate
negative contribution estimate. No original physical-response alignment,
global negative-tail bound, outer physical pair-Haar floor, all-physical
Hilbert coercivity or continuum mass gap is claimed unconditionally.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "cap" => p4Q2PZ37ABV_pairCap
local instance p4Q2PZ37ABW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABW_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABW_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABW_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ABW_links : Fintype Link := Fintype.ofFinite _
local notation "response" => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num)
local notation "pair" => p4Q2PZ37ABT_originalSignedPair H
local notation "det" => p4Q2PZ37ABU_originalPosteriorDet H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

/-- The ACTUAL ABT pair is the original physical response difference times
ABU's determinant of the two interacting posterior density rows. -/
theorem p4Q2PZ37ABW_originalPair_eq_receiver_mul_det
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (g h : G) :
    pair b hb f e z (g, h) =
      (response b hb f e (z, g) - response b hb f e (z, h)) *
        det b hb z.2 e g h := rfl

/-- A genuine receiver margin on the already-positive ABV region gives
a pointwise floor for the same original physical signed pairing. -/
theorem p4Q2PZ37ABW_originalPair_lower_on_cap
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (η : ℝ) (hη : 0 ≤ η)
    (hAlign : ∀ g h : G, (g, h) ∈ cap →
      η ≤ response b hb f e (z, g) - response b hb f e (z, h))
    (g h : G) (hcap : (g, h) ∈ cap) :
    η * (Real.exp (-32 * b) * (2 * b)) ≤ pair b hb f e z (g, h) := by
  have hd := p4Q2PZ37ABV_originalDet_lower_on_pairCap H b hb z.2 e g h hcap
  have hd0 : 0 ≤ det b hb z.2 e g h :=
    le_trans (by positivity) hd
  rw [p4Q2PZ37ABW_originalPair_eq_receiver_mul_det]
  calc
    η * (Real.exp (-32 * b) * (2 * b)) ≤ η * det b hb z.2 e g h :=
      mul_le_mul_of_nonneg_left hd hη
    _ ≤ (response b hb f e (z, g) - response b hb f e (z, h)) *
          det b hb z.2 e g h :=
      mul_le_mul_of_nonneg_right (hAlign g h hcap) hd0

/-- The actual signed physical pair is nonnegative on U under the
explicit receiver-alignment hypothesis, not unconditionally. -/
theorem p4Q2PZ37ABW_originalPair_nonneg_on_cap
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (η : ℝ) (hη : 0 ≤ η)
    (hAlign : ∀ g h : G, (g, h) ∈ cap →
      η ≤ response b hb f e (z, g) - response b hb f e (z, h))
    (g h : G) (hcap : (g, h) ∈ cap) :
    0 ≤ pair b hb f e z (g, h) :=
  le_trans (by positivity)
    (p4Q2PZ37ABW_originalPair_lower_on_cap H b hb f e z η hη hAlign g h hcap)

/-- Restricted integral of the original physical signed receiver:
the lower bound is volume/link/background independent IF its margin is. -/
theorem p4Q2PZ37ABW_originalPair_cap_integral_lower
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (η : ℝ) (hη : 0 ≤ η)
    (hAlign : ∀ g h : G, (g, h) ∈ cap →
      η ≤ response b hb f e (z, g) - response b hb f e (z, h)) :
    η * b * Real.exp (-32 * b) / 32 ≤
      ∫ w in cap, pair b hb f e z w ∂(Measure.prod μ μ) := by
  have hset :
      (η * (Real.exp (-32 * b) * (2 * b))) *
          Measure.real (Measure.prod μ μ) cap ≤
        ∫ w in cap, pair b hb f e z w ∂(Measure.prod μ μ) :=
    setIntegral_ge_of_const_le_real p4Q2PZ37ABV_pairCap_measurable
      (measure_ne_top _ _)
      (fun w hw =>
        p4Q2PZ37ABW_originalPair_lower_on_cap H b hb f e z η hη hAlign w.1 w.2 hw)
      (p4Q2PZ37ABT_originalSignedPair_integrable H b hb f e z).integrableOn
  calc
    η * b * Real.exp (-32 * b) / 32 =
      (η * (Real.exp (-32 * b) * (2 * b))) * (1 / 64 : ℝ) := by ring
    _ ≤ (η * (Real.exp (-32 * b) * (2 * b))) *
          Measure.real (Measure.prod μ μ) cap :=
      mul_le_mul_of_nonneg_left p4Q2PZ37ABV_pairCap_real_mass_lower (by positivity)
    _ ≤ _ := hset

/-- The positive PART of the FULL ABT signed pair is at least its cap
contribution. The complementary and negative contributions are not erased. -/
theorem p4Q2PZ37ABW_originalPair_positive_part_mass_lower
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (η : ℝ) (hη : 0 ≤ η)
    (hAlign : ∀ g h : G, (g, h) ∈ cap →
      η ≤ response b hb f e (z, g) - response b hb f e (z, h)) :
    η * b * Real.exp (-32 * b) / 32 ≤
      ∫ w : G × G, max (pair b hb f e z w) 0 ∂(Measure.prod μ μ) := by
  have hpair := p4Q2PZ37ABT_originalSignedPair_integrable H b hb f e z
  have hpos : Integrable (fun w : G × G => max (pair b hb f e z w) 0)
      (Measure.prod μ μ) :=
    ((p4Q2PZ37ABT_originalSignedPair_continuous H b hb f e z).max
      continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcap_le_pos :
      (∫ w in cap, pair b hb f e z w ∂(Measure.prod μ μ)) ≤
        ∫ w in cap, max (pair b hb f e z w) 0 ∂(Measure.prod μ μ) :=
    setIntegral_mono_on hpair.integrableOn hpos.integrableOn
      p4Q2PZ37ABV_pairCap_measurable (by
        intro w hw
        exact le_max_left _ _)
  have hpos_ae : ∀ᵐ w : G × G ∂(Measure.prod μ μ),
      0 ≤ max (pair b hb f e z w) 0 :=
    Filter.Eventually.of_forall (fun w => le_max_right _ _)
  have hcap_to_full :
      (∫ w in cap, max (pair b hb f e z w) 0 ∂(Measure.prod μ μ)) ≤
        ∫ w : G × G, max (pair b hb f e z w) 0 ∂(Measure.prod μ μ) :=
    setIntegral_le_integral (s := cap) hpos hpos_ae
  exact (p4Q2PZ37ABW_originalPair_cap_integral_lower
    H b hb f e z η hη hAlign).trans (hcap_le_pos.trans hcap_to_full)

/-- Exact original GI response: if the COMPLETE negative-part integral
is bounded by N, the cap margin gives a quantitative full GI lower bound. -/
theorem p4Q2PZ37ABW_originalGI_lower_of_negative_tail
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (η N : ℝ) (hη : 0 ≤ η)
    (hAlign : ∀ g h : G, (g, h) ∈ cap →
      η ≤ response b hb f e (z, g) - response b hb f e (z, h))
    (hN : (∫ w : G × G, max (-pair b hb f e z w) 0 ∂(Measure.prod μ μ)) ≤ N) :
    (η * b * Real.exp (-32 * b) / 32 - N) / 2 ≤ gap b hb f e z :=
  p4Q2PZ37ABT_originalGI_lower_of_pair_mass_bounds H b hb f e z
    (η * b * Real.exp (-32 * b) / 32) N
    (p4Q2PZ37ABW_originalPair_positive_part_mass_lower H b hb f e z η hη hAlign)
    hN

/-- A complementary signed integral bound gives an alternative exact GI
estimate without substituting any independent posterior or omitting tails. -/
theorem p4Q2PZ37ABW_originalGI_lower_of_complement_signed_tail
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (η N : ℝ) (hη : 0 ≤ η)
    (hAlign : ∀ g h : G, (g, h) ∈ cap →
      η ≤ response b hb f e (z, g) - response b hb f e (z, h))
    (hOutside : -N ≤
      ∫ w in capᶜ, pair b hb f e z w ∂(Measure.prod μ μ)) :
    (η * b * Real.exp (-32 * b) / 32 - N) / 2 ≤ gap b hb f e z := by
  have hcap := p4Q2PZ37ABW_originalPair_cap_integral_lower
    H b hb f e z η hη hAlign
  have hdecomp := integral_add_compl p4Q2PZ37ABV_pairCap_measurable
    (p4Q2PZ37ABT_originalSignedPair_integrable H b hb f e z)
  have htotal :
      η * b * Real.exp (-32 * b) / 32 - N ≤
        ∫ w : G × G, pair b hb f e z w ∂(Measure.prod μ μ) := by
    rw [← hdecomp]
    linarith
  rw [p4Q2PZ37ABT_originalGI_eq_half_pair_integral]
  linarith

/-- Strictly positive ORIGINAL GI response follows only if a verified
receiver margin beats the entire original negative tail. The premise
is intentionally NOT asserted for arbitrary physical sources. -/
theorem p4Q2PZ37ABW_originalGI_pos_of_negative_tail_margin
    (b : ℝ) (hb : 0 < b) (f : Phys) (e : Link)
    (z : Cfg × Cfg) (η N : ℝ) (hη : 0 ≤ η)
    (hAlign : ∀ g h : G, (g, h) ∈ cap →
      η ≤ response b hb.le f e (z, g) - response b hb.le f e (z, h))
    (hN : (∫ w : G × G, max (-pair b hb.le f e z w) 0 ∂(Measure.prod μ μ)) ≤ N)
    (hMargin : N < η * b * Real.exp (-32 * b) / 32) :
    0 < gap b hb.le f e z := by
  have hbound := p4Q2PZ37ABW_originalGI_lower_of_negative_tail
    H b hb.le f e z η N hη hAlign hN
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalPair_eq_receiver_mul_det
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalPair_lower_on_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalPair_nonneg_on_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalPair_cap_integral_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalPair_positive_part_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalGI_lower_of_negative_tail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalGI_lower_of_complement_signed_tail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABW_originalGI_pos_of_negative_tail_margin
