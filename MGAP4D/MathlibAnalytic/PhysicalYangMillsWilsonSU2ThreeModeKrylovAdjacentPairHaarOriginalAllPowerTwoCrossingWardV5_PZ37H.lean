import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCutCenterHaarV5_PZ37H
import Mathlib.Tactic

/-!
# PZ37H — all spatial powers: original two-crossing Haar Ward

The original centre-cut and vertex-gauge selection rules remove every
weighted single trace and distinct pair of temporal traces. Diagonal
single-link energy powers use the genuine full SU(2) vertex gauge Ward.
Integrate the actual finite double-link expansion of the original Cross².
This proves F(i,2) boundary-invariant for EVERY natural i and finite H,
including i=0 and H=0, without an independence hypothesis.

In particular F(4,2) drops from PZ37G's alternating boundary determinant.
The exact physical seventh six-moment Taylor jet retains F(2,4) alone:
  C7jet = -V/512 - [w,F(2,4)]/16.
No vanishing of the last sector, eighth-order analytic remainder,
rank-three witness, uniform coercivity, or mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37H_ward_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37H_ward_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37H_ward_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37H_ward_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37H_ward_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37H_ward_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ37H_ward_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section AllSpatialPowerTwoCrossing
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "τ" => p4Q2PZ37H_originalTemporalTrace H
local notation "F" => p4Q2PZ37D_originalMixedHaar H
local notation "W" => p4Q2PZ37B_originalBoundaryWedge H
local notation "I" => (fun _ : Link => (1 : G))

/-- The genuine vertex-gauge Ward works for every spatial Wilson power
and every power of a SINGLE original temporal-link energy. -/
theorem p4Q2PZ37H_originalSpatialPower_singleLinkPower_invariant
    (i k : ℕ) (e : Link) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*(E ((X e)⁻¹*B e))^k ∂haar) =
      (∫ X : Cfg, (w X)^i*(E ((X e)⁻¹))^k ∂haar) := by
  classical
  let γ : Gauge := fun v => if v = e.1 then B e else 1
  have hsrc : γ e.1 = B e := by simp [γ]
  have htar : γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [γ, p4Q2PL_originalSpatialLink_target_ne_source H e]
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hT : MeasurePreserving T haar haar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
  have hRel (X : Cfg) : (T X e)⁻¹*B e = (X e)⁻¹ := by
    change (γ e.1*X e*
      (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹)⁻¹*B e = _
    rw [hsrc, htar]
    group
  have hw (X : Cfg) : w (T X) = w X := by
    unfold p4Q2PS_originalHalfSpatialAction
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant]
  have hc : Continuous (fun X : Cfg => (w X)^i*(E ((X e)⁻¹*B e))^k) :=
    ((p4Q2PZ36C_half_continuous H).pow i).mul
      (((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
        ((continuous_apply e).inv.mul continuous_const)).pow k)
  calc
    (∫ X : Cfg, (w X)^i*(E ((X e)⁻¹*B e))^k ∂haar) =
        (∫ X : Cfg, (w (T X))^i*(E ((T X e)⁻¹*B e))^k ∂haar) :=
      p4Q2PZ37H_originalHaar_change H T hT _ hc
    _ = (∫ X : Cfg, (w X)^i*(E ((X e)⁻¹))^k ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      rw [hw X, hRel X]

/-- Every original distinct-link ENERGY pairing equals the actual spatial
Haar mean. Each trace term is removed by a proven original symmetry. -/
theorem p4Q2PZ37H_originalSpatialPower_distinctEnergyPair_mean
    (i : ℕ) (e f : Link) (hef : e ≠ f) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*(E ((X e)⁻¹*B e)*E ((X f)⁻¹*B f)) ∂haar) =
      (∫ X : Cfg, (w X)^i ∂haar) := by
  let g0 : Cfg → ℝ := fun X => (w X)^i
  let ge : Cfg → ℝ := fun X => (w X)^i*τ e X B
  let gf : Cfg → ℝ := fun X => (w X)^i*τ f X B
  let gef : Cfg → ℝ := fun X => (w X)^i*(τ e X B*τ f X B)
  have hc0 : Continuous g0 := (p4Q2PZ36C_half_continuous H).pow i
  have hce : Continuous ge := hc0.mul (p4Q2PZ37H_originalTemporalTrace_continuous H e B)
  have hcf : Continuous gf := hc0.mul (p4Q2PZ37H_originalTemporalTrace_continuous H f B)
  have hcef : Continuous gef := hc0.mul
    ((p4Q2PZ37H_originalTemporalTrace_continuous H e B).mul
      (p4Q2PZ37H_originalTemporalTrace_continuous H f B))
  have hi0 : Integrable g0 haar :=
    hc0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hie : Integrable ge haar :=
    hce.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hif : Integrable gf haar :=
    hcf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hief : Integrable gef haar :=
    hcef.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ X : Cfg, (w X)^i*(E ((X e)⁻¹*B e)*E ((X f)⁻¹*B f)) ∂haar) =
        (∫ X : Cfg, (g0 X-ge X)-gf X+gef X ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      dsimp [g0, ge, gf, gef, p4Q2PZ37H_originalTemporalTrace]
      ring
    _ = ((∫ X : Cfg, g0 X ∂haar)-(∫ X : Cfg, ge X ∂haar))-
        (∫ X : Cfg, gf X ∂haar)+(∫ X : Cfg, gef X ∂haar) := by
      rw [integral_add ((hi0.sub hie).sub hif) hief,
        integral_sub (hi0.sub hie) hif, integral_sub hi0 hie]
    _ = (∫ X : Cfg, (w X)^i ∂haar) := by
      change ((∫ X : Cfg, (w X)^i ∂haar)-
        (∫ X : Cfg, (w X)^i*τ e X B ∂haar))-
        (∫ X : Cfg, (w X)^i*τ f X B ∂haar)+
        (∫ X : Cfg, (w X)^i*(τ e X B*τ f X B) ∂haar) = _
      rw [p4Q2PZ37H_originalSpatialPower_oneTrace_zero H i e B,
        p4Q2PZ37H_originalSpatialPower_oneTrace_zero H i f B,
        p4Q2PZ37H_originalSpatialPower_twoDistinctTraces_zero H i e f hef B]
      ring

/-- Literal finite double-link expansion of the full original crossing square,
with compact-Haar integrability justified for every summand. -/
theorem p4Q2PZ37H_originalSpatialPower_crossingSquare_pairSum
    (i : ℕ) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*(Cross X B)^2 ∂haar) =
      ∑ e : Link, ∑ f : Link,
        ∫ X : Cfg, (w X)^i*(E ((X e)⁻¹*B e)*E ((X f)⁻¹*B f)) ∂haar := by
  classical
  let g : Link → Link → Cfg → ℝ := fun e f X =>
    (w X)^i*(E ((X e)⁻¹*B e)*E ((X f)⁻¹*B f))
  have hE (e : Link) : Continuous (fun X : Cfg => E ((X e)⁻¹*B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hc (e f : Link) : Continuous (g e f) :=
    ((p4Q2PZ36C_half_continuous H).pow i).mul ((hE e).mul (hE f))
  have hi (e f : Link) : Integrable (g e f) haar :=
    (hc e f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcSum (e : Link) : Continuous (fun X : Cfg => ∑ f : Link, g e f X) := by
    apply continuous_finset_sum
    intro f _hf
    exact hc e f
  have hiSum (e : Link) : Integrable (fun X : Cfg => ∑ f : Link, g e f X) haar :=
    (hcSum e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCross (X : Cfg) : Cross X B = ∑ e : Link, E ((X e)⁻¹*B e) := by
    simp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction,
      periodicHypercubicEvenSpatialSliceLinkList]
  have hPoint (X : Cfg) : (w X)^i*(Cross X B)^2 =
      ∑ e : Link, ∑ f : Link, g e f X := by
    simp only [hCross X, pow_two, Finset.sum_mul, Finset.mul_sum, g]
  calc
    (∫ X : Cfg, (w X)^i*(Cross X B)^2 ∂haar) =
        (∫ X : Cfg, ∑ e : Link, ∑ f : Link, g e f X ∂haar) := by
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = ∑ e : Link, ∫ X : Cfg, ∑ f : Link, g e f X ∂haar :=
      integral_finset_sum Finset.univ (f := fun e X => ∑ f : Link, g e f X)
        (fun e _he => hiSum e)
    _ = ∑ e : Link, ∑ f : Link, ∫ X : Cfg, g e f X ∂haar := by
      apply Finset.sum_congr rfl
      intro e _he
      exact integral_finset_sum Finset.univ (f := g e) (fun f _hf => hi e f)

/-- All original spatial Wilson powers have boundary-independent two-crossing
Haar response, including all minimal-period and diagonal-link cases. -/
theorem p4Q2PZ37H_originalSpatialPower_crossingSquare_invariant
    (i : ℕ) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*(Cross X B)^2 ∂haar) =
      (∫ X : Cfg, (w X)^i*(Cross X I)^2 ∂haar) := by
  classical
  rw [p4Q2PZ37H_originalSpatialPower_crossingSquare_pairSum H i B,
    p4Q2PZ37H_originalSpatialPower_crossingSquare_pairSum H i I]
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases hef : e = f
  · subst f
    simpa only [pow_two, mul_one] using
      (p4Q2PZ37H_originalSpatialPower_singleLinkPower_invariant H i 2 e B)
  · rw [p4Q2PZ37H_originalSpatialPower_distinctEnergyPair_mean H i e f hef B,
      p4Q2PZ37H_originalSpatialPower_distinctEnergyPair_mean H i e f hef I]

/-- The existing original F(i,2) definition now has a uniform-in-degree
boundary Ward identity. This is not a volume-uniform coercivity estimate. -/
theorem p4Q2PZ37H_originalMixedTwo_boundaryInvariant
    (i : ℕ) (B : Cfg) : F i 2 B = F i 2 I :=
  p4Q2PZ37H_originalSpatialPower_crossingSquare_invariant H i B

/-- The formerly unknown F(4,2) sector is constant and vanishes only in the
boundary difference. Its Haar value itself is not set to zero. -/
theorem p4Q2PZ37H_originalSixthWedge_oneSector
    (A B C : Cfg) :
    W w (fun D : Cfg => 45*F 2 4 D+225*F 4 2 D) A B C =
      45*W w (F 2 4) A B C := by
  unfold p4Q2PZ37B_originalBoundaryWedge
  dsimp only
  rw [p4Q2PZ37H_originalMixedTwo_boundaryInvariant H 4 A,
    p4Q2PZ37H_originalMixedTwo_boundaryInvariant H 4 B,
    p4Q2PZ37H_originalMixedTwo_boundaryInvariant H 4 C]
  ring

/-- Exact original physical seventh jet, with the single surviving genuine
F(2,4) Haar obstruction retained and the factorial 45/720 reduced to 1/16. -/
theorem p4Q2PZ37H_originalPhysicalSeventhJet_oneObstruction
    (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 -
        W w (F 2 4) A B C/16 := by
  rw [p4Q2PZ37G_originalPhysicalSeventhJet_twoEvenObstructions H A B C,
    p4Q2PZ37H_originalSixthWedge_oneSector H A B C]
  ring

/-- The proposed pure Vandermonde value is now equivalent to precisely ONE
original Haar condition; that remaining condition is not presumed true. -/
theorem p4Q2PZ37H_originalPhysicalSeventhJet_vandermonde_iff
    (A B C : Cfg) :
    p4Q2PZ37B_originalPhysicalSeventhCoefficient H A B C =
      -(PZ37VandermondeAlgebra.vandermonde (w A) (w B) (w C))/512 ↔
        W w (F 2 4) A B C = 0 := by
  rw [p4Q2PZ37H_originalPhysicalSeventhJet_oneObstruction H A B C]
  constructor <;> intro h <;> linarith

end AllSpatialPowerTwoCrossing
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalSpatialPower_singleLinkPower_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalSpatialPower_distinctEnergyPair_mean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalSpatialPower_crossingSquare_pairSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalSpatialPower_crossingSquare_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalMixedTwo_boundaryInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalSixthWedge_oneSector
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalPhysicalSeventhJet_oneObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalPhysicalSeventhJet_vandermonde_iff
