import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoRadiusAntipodalHaarObstructionV5_PZ37ADO
import Mathlib.Topology.Compactness.Bases
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADP — genuine small-radius Haar finite-net certificates

ADK/ADM already establish actual normalized compact Haar SU(2) chordal
balls B_J(a,r), center-independent mass m(r), and m(r)>0 for all r>0.
ADL/ADM establish the original finite-H two-boundary Haar product law
and the true all-link D_H ball's radial-power lower estimate.

ADP gives an EVALUABLE FINITE-COVER CERTIFICATE interface without
substituting Haar, physical source, Wilson FF receiver or posteriors:

For any finite net s of ACTUAL SU(2) group points whose true chordal
balls of radius r cover the whole compact group, the exact original
Haar measure satisfies

          1 <= |s| * m(r),  hence  1/|s| <= m(r).

Such a finite net exists for EVERY r>0 because all these ORIGINAL
feature balls are open in the original topology and SU(2) is compact.

For any certified cardinality |s| <= N with N>0 one obtains the
checkable REAL NUMERICAL bound m(r) >= 1/N. Thus one can certify
numeric small balls without a replacement finite-group Haar law.

At the original physical all-link radius R>0, choose the true one-link
radius r=R/(2*card(Link_H)+1). Any valid same actual SU(2) net
certificate yields the explicit H-dependent floor
    ν_H(B_{D_H}(a,R)) >= (1/|s|)^(2*card(Link_H)).
The original covariance moment lower bounds from ADM can then
reuse these very SAME full balls, if separately quantified.

This file does NOT compute N as a function of r. In particular
the mere existence of a finite net does not yet provide a closed-form
numeric lower bound such as c*r^3, nor a numerical Lipschitz modulus,
ADI/ADH strict 68 success, H-uniform coercivity or the continuum gap.
Constructing a radius-explicit grid in the genuine four-real-dimensional
SU(2) matrix/quaternion subspace remains the next obstruction.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "haar" => normalizedCompactHaar G
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass

local instance p4Q2PZ37ADP_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADP_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADP_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADP_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADP_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADP_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- An ACTUAL finite set of original SU(2) centers is a
radius-r net exactly when every original group element has one
certified feature-chordal center within distance <r. -/
def p4Q2PZ37ADP_isTrueChordalNet (s : Finset G) (r : ℝ) : Prop :=
  ∀ g : G, ∃ a ∈ s, dJ a g < r

/-- Original compact SU(2) always admits a FINITE net at every
positive radius, by the actual open calibrated Wilson-feature balls.
No quantitative count has been assumed or inserted. -/
theorem p4Q2PZ37ADP_exists_trueFiniteChordalNet
    (r : ℝ) (hr : 0 < r) :
    ∃ s : Finset G, p4Q2PZ37ADP_isTrueChordalNet s r := by
  have hOpen (a : G) : IsOpen (BallJ a r) :=
    p4Q2PZ37ADK_trueChordalBall_isOpen a r
  have hCover : (Set.univ : Set G) ⊆ ⋃ a : G, BallJ a r := by
    intro g _hg
    exact Set.mem_iUnion.mpr
      ⟨g, p4Q2PZ37ADK_trueChordalBall_mem_center g r hr⟩
  obtain ⟨s, hs⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set G)).elim_finite_subcover
      (fun a : G => BallJ a r) hOpen hCover
  refine ⟨s, ?_⟩
  intro g
  have hg := hs (Set.mem_univ g)
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hg
  obtain ⟨has, hag⟩ := Set.mem_iUnion.mp ha
  exact ⟨a, has, hag⟩

/-- Each original genuine covering net is nonempty (the original
SU(2) group has the identity). This ensures an actual positive
cardinality for the reciprocal mass certificate. -/
theorem p4Q2PZ37ADP_trueChordalNet_nonempty
    (s : Finset G) (r : ℝ)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s r) :
    s.Nonempty := by
  obtain ⟨a, ha, _⟩ := hs (1 : G)
  exact ⟨a, ha⟩

/-- The original SU(2) full group is covered by the same
finite union of true open Wilson-feature balls from any net. -/
theorem p4Q2PZ37ADP_trueChordalNet_cover_univ
    (s : Finset G) (r : ℝ)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s r) :
    (Set.univ : Set G) ⊆ ⋃ a ∈ s, BallJ a r := by
  intro g _hg
  obtain ⟨a, ha, hag⟩ := hs g
  exact Set.mem_iUnion.mpr
    ⟨a, Set.mem_iUnion.mpr ⟨ha, hag⟩⟩

/-- A finite cover by ACTUAL original SU(2) Haar balls has
total original Haar mass at least one; center independence
therefore produces an exact reciprocal-cardinality certificate.
No finite counting measure replaces normalized compact Haar. -/
theorem p4Q2PZ37ADP_trueFiniteNet_HaarMass_card_mul_ge_one
    (s : Finset G) (r : ℝ)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s r) :
    1 ≤ (s.card : ℝ) * m r := by
  have hCover := p4Q2PZ37ADP_trueChordalNet_cover_univ s r hs
  have hBound :
      (1 : ℝ) ≤ ∑ a ∈ s, Measure.real haar (BallJ a r) := by
    calc
      (1 : ℝ) = Measure.real haar (Set.univ : Set G) := by simp
      _ ≤ Measure.real haar (⋃ a ∈ s, BallJ a r) :=
        measureReal_mono hCover (measure_ne_top _ _)
      _ ≤ ∑ a ∈ s, Measure.real haar (BallJ a r) :=
        measureReal_biUnion_finset_le s (fun a : G => BallJ a r)
  simp_rw [p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial] at hBound
  simpa [Finset.sum_const, nsmul_eq_mul] using hBound

/-- Numerical original Haar certificate for ANY physical SU(2)
finite set s whose true chordal radius-r balls cover the group.
Its denominator is the ACTUAL number of group centers, not a free
constant or an arbitrary substitute probability law. -/
theorem p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_reciprocal
    (s : Finset G) (r : ℝ)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s r) :
    1 / (s.card : ℝ) ≤ m r := by
  have hPos : (0 : ℝ) < s.card := by
    exact_mod_cast (Finset.card_pos.mpr
      (p4Q2PZ37ADP_trueChordalNet_nonempty s r hs))
  apply (div_le_iff₀ hPos).mpr
  have hMass :=
    p4Q2PZ37ADP_trueFiniteNet_HaarMass_card_mul_ge_one s r hs
  nlinarith only [hMass]

/-- An actual certified net with size at most a chosen concrete
positive natural N yields the NUMERIC ORIGINAL Haar floor 1/N.
Checking the finite cover is the only remaining certificate premise. -/
theorem p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_inverse_budget
    (s : Finset G) (r : ℝ) (N : ℕ)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s r)
    (hCard : s.card ≤ N) :
    1 / (N : ℝ) ≤ m r := by
  have hsPos : (0 : ℝ) < s.card := by
    exact_mod_cast (Finset.card_pos.mpr
      (p4Q2PZ37ADP_trueChordalNet_nonempty s r hs))
  have hN : (0 : ℝ) < N := by
    have hCardReal : (s.card : ℝ) ≤ N := by exact_mod_cast hCard
    linarith
  have hCardReal : (s.card : ℝ) ≤ N := by exact_mod_cast hCard
  have hInv : (1 : ℝ) / N ≤ 1 / (s.card : ℝ) :=
    (div_le_div_iff₀ hN hsPos).mpr (by nlinarith only [hCardReal])
  exact hInv.trans
    (p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_reciprocal s r hs)

/-- Unconditionally, every original SU(2) small positive radius
admits a certificate with an actual FINITE integer denominator.
Unlike ADM's qualitative positivity this carries a checkable
finite-cover witness, but the integer is not yet given by r-formula. -/
theorem p4Q2PZ37ADP_everyPositiveRadius_hasFiniteNumericCertificate
    (r : ℝ) (hr : 0 < r) :
    ∃ s : Finset G,
      s.Nonempty ∧ p4Q2PZ37ADP_isTrueChordalNet s r ∧
        1 / (s.card : ℝ) ≤ m r := by
  obtain ⟨s, hs⟩ := p4Q2PZ37ADP_exists_trueFiniteChordalNet r hr
  exact ⟨s,
    p4Q2PZ37ADP_trueChordalNet_nonempty s r hs,
    hs,
    p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_reciprocal s r hs⟩

/-- The same TRUE normalized compact Haar lower bound holds at
every genuine original SU(2) center. No law or radius changes. -/
theorem p4Q2PZ37ADP_trueFiniteNet_allCenters_HaarMass_ge
    (s : Finset G) (r : ℝ)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s r)
    (a : G) :
    1 / (s.card : ℝ) ≤
      Measure.real haar (BallJ a r) := by
  rw [p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial]
  exact p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_reciprocal s r hs

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H

local instance p4Q2PZ37ADP_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADP_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A finite-cover certificate of ORIGINAL one-link Haar at radius
r=R/(2*card(Link_H)+1) gives a fully explicit original physical
pair-Haar full metric ball bound with true 2*card(Link_H) exponent. -/
theorem p4Q2PZ37ADP_originalFullBall_ge_finiteNetPower
    (a : Pair) (R : ℝ) (hR : 0 < R)
    (s : Finset G)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s
      (R / (2 * (Fintype.card Link : ℝ) + 1))) :
    (1 / (s.card : ℝ)) ^ (2 * Fintype.card Link) ≤
      Measure.real outer (Ball a R) := by
  have hOne :=
    p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_reciprocal
      s (R / (2 * (Fintype.card Link : ℝ) + 1)) hs
  have hPow :=
    pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ 1 / (s.card : ℝ))
      hOne (2 * Fintype.card Link)
  exact hPow.trans
    (p4Q2PZ37ADM_originalFullBall_mass_ge_radialPower H a R hR)

/-- Any checkably certified N-point budget gives the original
full all-link D_H ball numeric Haar lower bound N^(-2*card).
This is an authentic original pair-Haar statement, with no
substitute finite probability and no H-uniform floor asserted. -/
theorem p4Q2PZ37ADP_originalFullBall_ge_budgetPower
    (a : Pair) (R : ℝ) (hR : 0 < R)
    (s : Finset G) (N : ℕ)
    (hs : p4Q2PZ37ADP_isTrueChordalNet s
      (R / (2 * (Fintype.card Link : ℝ) + 1)))
    (hCard : s.card ≤ N) :
    (1 / (N : ℝ)) ^ (2 * Fintype.card Link) ≤
      Measure.real outer (Ball a R) := by
  have hOne :=
    p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_inverse_budget
      s (R / (2 * (Fintype.card Link : ℝ) + 1)) N hs hCard
  exact (pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
    hOne _).trans
      (p4Q2PZ37ADM_originalFullBall_mass_ge_radialPower H a R hR)

/-- At every positive original finite-volume D_H radius there
is an ACTUAL finite SU(2) center set certifying an H-dependent
explicit reciprocal-power original pair-Haar mass lower bound.
No computable radius-only covering count is silently claimed. -/
theorem p4Q2PZ37ADP_originalFullBall_hasFiniteNetCertificate
    (a : Pair) (R : ℝ) (hR : 0 < R) :
    ∃ s : Finset G, s.Nonempty ∧
      p4Q2PZ37ADP_isTrueChordalNet s
        (R / (2 * (Fintype.card Link : ℝ) + 1)) ∧
      (1 / (s.card : ℝ)) ^ (2 * Fintype.card Link) ≤
        Measure.real outer (Ball a R) := by
  have hDen : (0 : ℝ) < 2 * (Fintype.card Link : ℝ) + 1 := by
    positivity
  have hr : 0 < R / (2 * (Fintype.card Link : ℝ) + 1) :=
    div_pos hR hDen
  obtain ⟨s, hs⟩ :=
    p4Q2PZ37ADP_exists_trueFiniteChordalNet
      (R / (2 * (Fintype.card Link : ℝ) + 1)) hr
  exact ⟨s, p4Q2PZ37ADP_trueChordalNet_nonempty s _ hs,
    hs, p4Q2PZ37ADP_originalFullBall_ge_finiteNetPower H a R hR s hs⟩

/-- A concrete ORIGINAL full distance ball of radius 1/2 has an
actual finite SU(2) net witness for the same original pair Haar
numerical-power bound. The net size is still to be evaluated. -/
theorem p4Q2PZ37ADP_originalHalfBall_hasFiniteNetCertificate
    (a : Pair) :
    ∃ s : Finset G, s.Nonempty ∧
      p4Q2PZ37ADP_isTrueChordalNet s
        ((1 / 2 : ℝ) / (2 * (Fintype.card Link : ℝ) + 1)) ∧
      (1 / (s.card : ℝ)) ^ (2 * Fintype.card Link) ≤
        Measure.real outer (Ball a (1 / 2)) :=
  p4Q2PZ37ADP_originalFullBall_hasFiniteNetCertificate
    H a (1 / 2) (by norm_num)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_exists_trueFiniteChordalNet
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_trueChordalNet_nonempty
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_trueChordalNet_cover_univ
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_trueFiniteNet_HaarMass_card_mul_ge_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_reciprocal
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_trueFiniteNet_HaarMass_ge_inverse_budget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_everyPositiveRadius_hasFiniteNumericCertificate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADP_trueFiniteNet_allCenters_HaarMass_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADP_originalFullBall_ge_finiteNetPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADP_originalFullBall_ge_budgetPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADP_originalFullBall_hasFiniteNetCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADP_originalHalfBall_hasFiniteNetCertificate
