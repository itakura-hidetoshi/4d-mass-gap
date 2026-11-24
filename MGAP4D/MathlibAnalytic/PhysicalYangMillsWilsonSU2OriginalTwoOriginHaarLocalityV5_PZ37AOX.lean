import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalMovingFirstRowSlopeV5_PZ37AOV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOX — native two-origin Haar shifts and volume-free local action

Diagnostic candidate, separate from AOW. Use the two actual primary
origin links (0 and 3) of AMS. ANV proves that no other spatial
plaquette contains both, even at H=0. Instead of resampling the whole
volume, multiply just these two coordinates by independent Haar variables.
For fixed shifts this preserves the original full spatial Haar measure.
For fixed background and second shift the primary holonomy has exactly Haar
law in the first shift. Two applications of the existing local action
oscillation bound give 16, independently of H.

These are inputs to a conditional AOK moment and a volume-uniform
normalized row slope; neither is claimed by this candidate alone.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "nu" => normalizedCompactHaar G
local notation "E" => p4Q2PZ37AMS_primarySpatialSliceEdge
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
local notation "Rep" => periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AOX_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOX_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOX_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOX_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOX_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOX_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AOX_haarProbability : IsProbabilityMeasure nu :=
  normalizedCompactHaar_isProbabilityMeasure G
local instance p4Q2PZ37AOX_haarInvariant : Measure.IsHaarMeasure nu := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- Only the two actual original positive origin links are shifted. This
uses the original configuration, not a new lattice or plaquette variable. -/
noncomputable def p4Q2PZ37AOX_twoOriginShift
    (H : ℕ) (B : Cfg H 2) (u v : G) : Cfg H 2 :=
  fun e => B e * (if e = E H 0 then u else if e = E H 3 then v else 1)

local notation "R" => p4Q2PZ37AOX_twoOriginShift

private theorem p4Q2PZ37AOX_edge_ne
    (H : ℕ) (i j : Fin 4) (hij : i ≠ j) : E H i ≠ E H j := by
  intro h
  apply hij
  exact (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H).injective h

/-- For fixed shifts, the original entire spatial Haar measure is invariant. -/
theorem p4Q2PZ37AOX_twoOriginShift_haarMeasurePreserving
    (H : ℕ) (u v : G) :
    MeasurePreserving (fun B : Cfg H 2 => R H B u v) (Mu H 2) (Mu H 2) := by
  classical
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let f : Link → G → G :=
    fun e x => x * (if e = E H 0 then u else if e = E H 3 then v else 1)
  have hMP (e : Link) : MeasurePreserving (f e) nu nu := by
    simpa [f] using
      (normalizedCompactHaar_measurePreserving_mul_left_right G (1 : G)
        (if e = E H 0 then u else if e = E H 3 then v else 1))
  refine ⟨?_, ?_⟩
  · unfold p4Q2PZ37AOX_twoOriginShift
    refine measurable_pi_lambda _ ?_
    intro e
    exact (hMP e).measurable.comp (measurable_pi_apply e)
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    have hf : ∀ e : Link, AEMeasurable (f e) nu :=
      fun e => (hMP e).measurable.aemeasurable
    letI : ∀ e : Link, SigmaFinite (Measure.map (f e) nu) :=
      fun e => by
        rw [(hMP e).map_eq]
        infer_instance
    change Measure.map (fun B : Link → G => fun e => f e (B e))
      (Measure.pi fun _ : Link => nu) = Measure.pi (fun _ : Link => nu)
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact (hMP e).map_eq

private theorem p4Q2PZ37AOX_replace_originalValue
    (H : ℕ) (B : Cfg H 2) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Rep H 2 B target (B target) = B := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self
      H 2 B target (B target)
  · exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
      H 2 B target e (B target) he

private theorem p4Q2PZ37AOX_twoOriginShift_eq_replace
    (H : ℕ) (B : Cfg H 2) (u v : G) :
    R H B u v =
      Rep H 2 (Rep H 2 B (E H 0) (B (E H 0) * u)) (E H 3) (B (E H 3) * v) := by
  classical
  have h03 : E H 0 ≠ E H 3 := p4Q2PZ37AOJ_primaryOriginLinks_ne H
  funext e
  by_cases h0 : e = E H 0
  · subst e
    simp [p4Q2PZ37AOX_twoOriginShift, h03,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self]
  · by_cases h3 : e = E H 3
    · subst e
      simp [p4Q2PZ37AOX_twoOriginShift, h03.symm,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self]
    · simp [p4Q2PZ37AOX_twoOriginShift, h0, h3,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne]

/-- The original action oscillation costs at most 8 per actual shifted
link, hence at most 16 for the two origin links, uniformly in H. -/
theorem p4Q2PZ37AOX_twoOriginShift_action_sub_abs_le_sixteen
    (H : ℕ) (A B : Cfg H 2) (u v : G) :
    |S H 2 A (R H B u v) - S H 2 A B| ≤ 16 := by
  let B0 : Cfg H 2 := Rep H 2 B (E H 0) (B (E H 0) * u)
  let B1 : Cfg H 2 := Rep H 2 B0 (E H 3) (B (E H 3) * v)
  have h0 := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_continuousVacuumReplaceLink_sub_abs_le_eight
    H 2 (by norm_num) A B (E H 0) (B (E H 0) * u) (B (E H 0))
  rw [p4Q2PZ37AOX_replace_originalValue H B (E H 0)] at h0
  change |S H 2 A B0 - S H 2 A B| ≤ 8 at h0
  have h1 := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_continuousVacuumReplaceLink_sub_abs_le_eight
    H 2 (by norm_num) A B0 (E H 3) (B (E H 3) * v) (B0 (E H 3))
  rw [p4Q2PZ37AOX_replace_originalValue H B0 (E H 3)] at h1
  change |S H 2 A B1 - S H 2 A B0| ≤ 8 at h1
  rw [p4Q2PZ37AOX_twoOriginShift_eq_replace H B u v]
  change |S H 2 A B1 - S H 2 A B| ≤ 16
  calc
    _ = |(S H 2 A B1 - S H 2 A B0) + (S H 2 A B0 - S H 2 A B)| := by
      congr 1
      ring
    _ ≤ |S H 2 A B1 - S H 2 A B0| + |S H 2 A B0 - S H 2 A B| :=
      abs_add_le _ _
    _ ≤ 16 := by linarith only [h0, h1]

/-- At fixed background B and fixed second shift v, the genuine cyclic
primary holonomy is a left/right translate of the first Haar shift u. -/
theorem p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_haarMeasurePreserving
    (H : ℕ) (B : Cfg H 2) (v : G) :
    MeasurePreserving (fun u : G => Hol H 2 (R H B u v)) nu nu := by
  classical
  have h03 := p4Q2PZ37AOJ_primaryOriginLinks_ne H
  have h10 : E H 1 ≠ E H 0 := p4Q2PZ37AOX_edge_ne H 1 0 (by decide)
  have h13 : E H 1 ≠ E H 3 := p4Q2PZ37AOX_edge_ne H 1 3 (by decide)
  have h20 : E H 2 ≠ E H 0 := p4Q2PZ37AOX_edge_ne H 2 0 (by decide)
  have h23 : E H 2 ≠ E H 3 := p4Q2PZ37AOX_edge_ne H 2 3 (by decide)
  let L : G := (B (E H 2))⁻¹ * (B (E H 3) * v)⁻¹ * B (E H 0)
  let T : G := B (E H 1)
  have heq : (fun u : G => Hol H 2 (R H B u v)) = fun u => L * u * T := by
    funext u
    have h0 : R H B u v (E H 0) = B (E H 0) * u := by
      simp [p4Q2PZ37AOX_twoOriginShift]
    have h1 : R H B u v (E H 1) = B (E H 1) := by
      simp [p4Q2PZ37AOX_twoOriginShift, h10, h13]
    have h2 : R H B u v (E H 2) = B (E H 2) := by
      simp [p4Q2PZ37AOX_twoOriginShift, h20, h23]
    have h3 : R H B u v (E H 3) = B (E H 3) * v := by
      simp [p4Q2PZ37AOX_twoOriginShift, h03.symm]
    unfold p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy haarFinFourCyclicPlaquetteWord
    rw [haarFinFourCyclicNestedCoordinates_apply]
    change (R H B u v (E H 2))⁻¹ *
      ((R H B u v (E H 3))⁻¹ * (R H B u v (E H 0) * R H B u v (E H 1))) =
      L * u * T
    simp only [h0, h1, h2, h3, L, T, mul_assoc]
  rw [heq]
  exact normalizedCompactHaar_measurePreserving_mul_left_right G L T

/-- Exact two-origin conditional Haar integration, retaining every other
original link as fixed background. No independence of plaquettes assumed. -/
theorem p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_iteratedHaar
    (H : ℕ) (B : Cfg H 2) (f : G → ℝ)
    (hf : AEStronglyMeasurable f nu) :
    (∫ v : G, (∫ u : G, f (Hol H 2 (R H B u v)) ∂nu) ∂nu) =
      ∫ g : G, f g ∂nu := by
  have hInner (v : G) :
      (∫ u : G, f (Hol H 2 (R H B u v)) ∂nu) = ∫ g : G, f g ∂nu := by
    have hMP := p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_haarMeasurePreserving H B v
    have hfmap : AEStronglyMeasurable f
        (Measure.map (fun u : G => Hol H 2 (R H B u v)) nu) := by
      rw [hMP.map_eq]
      exact hf
    calc
      _ = ∫ g : G, f g ∂Measure.map (fun u : G => Hol H 2 (R H B u v)) nu :=
        (integral_map hMP.measurable.aemeasurable hfmap).symm
      _ = _ := by rw [hMP.map_eq]
  rw [show (fun v : G => ∫ u : G, f (Hol H 2 (R H B u v)) ∂nu) =
      (fun _ : G => ∫ g : G, f g ∂nu) by funext v; exact hInner v]
  simp

/-- The conditional zero-coupling first character moment vanishes on
every two-origin Haar fiber. -/
theorem p4Q2PZ37AOX_twoOriginShift_primaryCharacter_iteratedHaar_zero
    (H : ℕ) (B : Cfg H 2) :
    (∫ v : G, (∫ u : G, Chi (Hol H 2 (R H B u v)) ∂nu) ∂nu) = 0 := by
  rw [p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_iteratedHaar H B Chi
    GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.measurable.aestronglyMeasurable]
  exact GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero

/-- The conditional character second moment is 1/4 on EVERY such
fiber, including the smallest periodic volume. -/
theorem p4Q2PZ37AOX_twoOriginShift_primaryCharacter_iteratedHaar_secondMoment
    (H : ℕ) (B : Cfg H 2) :
    (∫ v : G, (∫ u : G, (Chi (Hol H 2 (R H B u v)))^2 ∂nu) ∂nu) = (1 / 4 : ℝ) := by
  rw [p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_iteratedHaar H B (fun g : G => (Chi g)^2)
    (GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.pow 2).measurable.aestronglyMeasurable]
  exact GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOX_twoOriginShift
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOX_twoOriginShift_haarMeasurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOX_twoOriginShift_action_sub_abs_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_haarMeasurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_iteratedHaar
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOX_twoOriginShift_primaryCharacter_iteratedHaar_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOX_twoOriginShift_primaryCharacter_iteratedHaar_secondMoment
