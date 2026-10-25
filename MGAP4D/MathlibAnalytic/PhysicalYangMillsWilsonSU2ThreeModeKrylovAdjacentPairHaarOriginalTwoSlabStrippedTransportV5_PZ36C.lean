import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalScaledMomentWardV5_PZ36A
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourLinkSchurTheoremV5_PZ35D9D
import Mathlib.Tactic

/-!
# PZ36C — actual two-slab stripped Haar transport through degree four

Keep the ORIGINAL two-slab Wilson action Q, the genuine normalized
spatial Haar measure, and the FULL middle weight 2*w(X). No independent
posterior, new measure, Schur premise, or moment-transport hypothesis.

The proof expands the inner Haar integral first, identifies its coefficients
by PZ36A with lambda=1, and then applies PZ36A with lambda=2 to the outer
integral. In particular it never discards the physical intermediate action.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36C_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36C_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36C_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36C_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36C_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36C_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36C_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalTwoSlabStrip
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))

/-- Original compact spatial half-action, not a replacement potential. -/
theorem p4Q2PZ36C_half_continuous : Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

/-- Original temporal crossing action with a fixed right boundary. -/
theorem p4Q2PZ36C_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hp : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using
    (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp

/-- Right-endpoint decomposition derived from the ACTUAL PS theorem;
this lemma only unfolds the already existing right-stripped action. -/
theorem p4Q2PZ36C_originalOneSlab_eq_rightStripped (A B : Cfg) :
    S A B = w A + Cross A B + w B := by
  simpa only [p4Q2PS_originalRightStrippedAction] using
    (p4Q2PS_originalOneSlabAction_rightSplit H A B)

/-- Algebraic identification with the actual original Q. The middle
spatial half-action occurs TWICE, once in each physical slab. -/
theorem p4Q2PZ36C_originalTwoSlab_strip_eq (Y X B : Cfg) :
    Q Y X B - w B =
      (w Y + Cross Y X) + (2*w X + Cross X B) := by
  change S Y X + S X B - w B = _
  rw [p4Q2PZ36C_originalOneSlab_eq_rightStripped H Y X,
    p4Q2PZ36C_originalOneSlab_eq_rightStripped H X B]
  change (w Y + Cross Y X + w X) +
    (w X + Cross X B + w B) - w B = _
  ring

/-- Genuine identity-boundary stripped left moments. -/
noncomputable def p4Q2PZ36C_originalStripMoment (k : ℕ) : ℝ :=
  ∫ Y : Cfg, (w Y + Cross Y I)^k ∂haar

/-- The actual inner two-slab stripped moment is a finite polynomial
in the TRUE middle/right action 2*w(X)+Cross(X,B). -/
theorem p4Q2PZ36C_originalInnerStrip_expansion
    (n : ℕ) (hn : n ≤ 4) (X B : Cfg) :
    (∫ Y : Cfg, (Q Y X B - w B)^n ∂haar) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (p4Q2PZ36C_originalStripMoment H k *
          (2*w X + Cross X B)^(n-k)) := by
  have hleft : Continuous (fun Y : Cfg => w Y + Cross Y X) :=
    (p4Q2PZ36C_half_continuous H).add (p4Q2PZ36C_cross_continuous H X)
  simp_rw [p4Q2PZ36C_originalTwoSlab_strip_eq H]
  rw [p4Q2PZ36A_originalHaar_integral_binomial H
    (fun Y : Cfg => w Y + Cross Y X)
    (fun _ : Cfg => 2*w X + Cross X B) hleft continuous_const n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk4 : k ≤ 4 := by
    have hk' := Finset.mem_range.mp hk
    omega
  have hMom : (∫ Y : Cfg, (w Y + Cross Y X)^k ∂haar) =
      p4Q2PZ36C_originalStripMoment H k := by
    simpa only [one_mul, p4Q2PZ36C_originalStripMoment] using
      (p4Q2PZ36A_originalScaledStripMoment_invariant_le_four H 1 k hk4 X)
  change (n.choose k : ℝ) *
      (∫ Y : Cfg, (w Y + Cross Y X)^k *
        (2*w X + Cross X B)^(n-k) ∂haar) = _
  rw [integral_mul_const, hMom]

/-- Continuity of the integrated inner moment is proved by its explicit
polynomial, not by assuming an unproved parameter-integral theorem. -/
theorem p4Q2PZ36C_originalInnerStrip_continuous
    (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    Continuous (fun X : Cfg => ∫ Y : Cfg, (Q Y X B-w B)^n ∂haar) := by
  have hR : Continuous (fun X : Cfg => 2*w X+Cross X B) :=
    (continuous_const.mul (p4Q2PZ36C_half_continuous H)).add
      (p4Q2PZ36C_cross_continuous H B)
  have heq : (fun X : Cfg => ∫ Y : Cfg, (Q Y X B-w B)^n ∂haar) =
      (fun X : Cfg => ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (p4Q2PZ36C_originalStripMoment H k *
          (2*w X+Cross X B)^(n-k))) := by
    funext X
    exact p4Q2PZ36C_originalInnerStrip_expansion H n hn X B
  rw [heq]
  apply continuous_finset_sum
  intro k _hk
  exact continuous_const.mul (continuous_const.mul (hR.pow (n-k)))

/-- Actual full double-Haar stripped moment as a finite sum of scaled
original right-slab Haar moments. No factorization of posteriors. -/
theorem p4Q2PZ36C_originalDoubleStrip_expansion
    (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    (∫ X : Cfg, (∫ Y : Cfg, (Q Y X B-w B)^n ∂haar) ∂haar) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (p4Q2PZ36C_originalStripMoment H k *
          (∫ X : Cfg, (2*w X+Cross X B)^(n-k) ∂haar)) := by
  have hR : Continuous (fun X : Cfg => 2*w X+Cross X B) :=
    (continuous_const.mul (p4Q2PZ36C_half_continuous H)).add
      (p4Q2PZ36C_cross_continuous H B)
  have hi (k : ℕ) : Integrable (fun X : Cfg => (n.choose k : ℝ) *
      (p4Q2PZ36C_originalStripMoment H k *
        (2*w X+Cross X B)^(n-k))) haar :=
    (continuous_const.mul (continuous_const.mul (hR.pow (n-k)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ X : Cfg, (∫ Y : Cfg, (Q Y X B-w B)^n ∂haar) ∂haar) =
      (∫ X : Cfg, ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (p4Q2PZ36C_originalStripMoment H k *
          (2*w X+Cross X B)^(n-k)) ∂haar) := by
        apply integral_congr_ae
        filter_upwards with X
        exact p4Q2PZ36C_originalInnerStrip_expansion H n hn X B
    _ = ∑ k ∈ Finset.range (n+1),
        (∫ X : Cfg, (n.choose k : ℝ) *
          (p4Q2PZ36C_originalStripMoment H k *
            (2*w X+Cross X B)^(n-k)) ∂haar) := by
      exact integral_finset_sum (Finset.range (n+1))
        (f := fun k (X : Cfg) => (n.choose k : ℝ) *
          (p4Q2PZ36C_originalStripMoment H k *
            (2*w X+Cross X B)^(n-k))) (fun k _hk => hi k)
    _ = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) *
        (p4Q2PZ36C_originalStripMoment H k *
          (∫ X : Cfg, (2*w X+Cross X B)^(n-k) ∂haar)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [integral_const_mul, integral_const_mul]

/-- The previously missing genuine TWO-slab degree-four stripped
Haar invariance, now with NO moment-transport assumption. -/
theorem p4Q2PZ36C_originalTwoSlabStrip_invariant_le_four
    (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    (∫ X : Cfg, (∫ Y : Cfg, (Q Y X B-w B)^n ∂haar) ∂haar) =
      (∫ X : Cfg, (∫ Y : Cfg, (Q Y X I-w I)^n ∂haar) ∂haar) := by
  rw [p4Q2PZ36C_originalDoubleStrip_expansion H n hn B,
    p4Q2PZ36C_originalDoubleStrip_expansion H n hn I]
  apply Finset.sum_congr rfl
  intro k _hk
  have hnk : n-k ≤ 4 := by omega
  rw [p4Q2PZ36A_originalScaledStripMoment_invariant_le_four H 2 (n-k) hnk B]

/-- Identity boundary has zero true half-action, so the invariant
stripped moment equals the actual unstripped two-slab identity moment. -/
theorem p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw
    (n : ℕ) (hn : n ≤ 4) (B : Cfg) :
    (∫ X : Cfg, (∫ Y : Cfg, (Q Y X B-w B)^n ∂haar) ∂haar) =
      (∫ X : Cfg, (∫ Y : Cfg, (Q Y X I)^n ∂haar) ∂haar) := by
  rw [p4Q2PZ36C_originalTwoSlabStrip_invariant_le_four H n hn B]
  simp only [p4Q2PZ35_originalHalfSpatialAction_identity_zero H, sub_zero]

end OriginalTwoSlabStrip
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36C_originalTwoSlab_strip_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36C_originalInnerStrip_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36C_originalInnerStrip_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36C_originalDoubleStrip_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36C_originalTwoSlabStrip_invariant_le_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36C_originalTwoSlabStrip_eq_identityRaw
