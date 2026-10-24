import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixthWardDecisionV5_PZ8
import Mathlib.Tactic

/-!
# P4-Q2-PZ9 — original off-diagonal plaquette-pair / triple-crossing Ward

The PZ8 sixth-order obstruction still requires actual SU(2) Haar
selection analysis. PY9B proves at least FOUR center-odd original
spatial links in the symmetric difference of distinct plaquettes,
including the exceptional period-two torus.

Three genuine temporal crossing insertions therefore leave a truly
center-odd spatial link UNUSED. The unchanged original product SU(2)
Haar measure kills the exact spatial plaquette-pair weighted triple
crossing. This extends the two-crossing PY9D Ward selection by one
order, without replacing the physical Wilson action or posteriors.

This off-diagonal fact alone does NOT prove W6 vanishes or differs
from zero; diagonal and further higher-order Haar terms remain open.
No mass-gap assertion, new axioms, sorry/admit or spectral proxies.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ9_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ9_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ9_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ9_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ9_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalPairThreeCrossingWard

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "s" => p4Q2PY9_originalPlaquettePhysicalEdges H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Flip" => p4Q2PU_originalSpatialSingleLinkCenterFlip H

/-- Among FOUR genuine center-odd links of distinct physical original
plaquettes, one remains after any THREE actual temporal crossings.
This also covers the physical even-period-two exceptional geometry. -/
theorem p4Q2PZ9_originalDistinctPlaquettes_oddFreeLink_for_threeCrossings
    (p q : Plaq) (hpq : p ≠ q) (e f g : Link) :
    ∃ target : Link,
      ((target ∈ s p ∧ target ∉ s q) ∨
        (target ∈ s q ∧ target ∉ s p)) ∧
      target ≠ e ∧ target ≠ f ∧ target ≠ g := by
  classical
  let odd := (s p \ s q) ∪ (s q \ s p)
  have hOdd : 4 ≤ odd.card :=
    p4Q2PY9_originalDistinctPlaquettes_oddEdges_card_ge_four H p q hpq
  have hThree : ({e, f, g} : Finset Link).card ≤ 3 :=
    Finset.card_le_three
  have hNonempty : (odd \ ({e, f, g} : Finset Link)).Nonempty :=
    Finset.sdiff_nonempty_of_card_lt_card (by omega)
  obtain ⟨target, htarget⟩ := hNonempty
  have hmem := Finset.mem_sdiff.mp htarget
  have hside := Finset.mem_union.mp hmem.1
  refine ⟨target, ?_, ?_, ?_, ?_⟩
  · rcases hside with hp | hq
    · exact Or.inl (Finset.mem_sdiff.mp hp)
    · exact Or.inr (Finset.mem_sdiff.mp hq)
  · intro h
    exact hmem.2 (by simp [h])
  · intro h
    exact hmem.2 (by simp [h])
  · intro h
    exact hmem.2 (by simp [h])

/-- True original spatial Haar center parity, conditional on a
plaquette-pair odd link that avoids three actual temporal crossings. -/
theorem p4Q2PZ9_originalPlaquettePair_tripleCrossingHaar_zero_of_freeLink
    (p q : Plaq) (e f g target : Link)
    (hp : target ∈ s p) (hq : target ∉ s q)
    (he : target ≠ e) (hf : target ≠ f) (hg : target ≠ g)
    (B : Cfg) :
    (∫ A : Cfg, (χ p A * χ q A) *
      (E ((A e)⁻¹ * B e) *
        E ((A f)⁻¹ * B f) *
        E ((A g)⁻¹ * B g)) ∂haar) = 0 := by
  let obs : Cfg → ℝ := fun A =>
    (χ p A * χ q A) *
      (E ((A e)⁻¹ * B e) *
        E ((A f)⁻¹ * B f) *
        E ((A g)⁻¹ * B g))
  have hChi (v : Plaq) :
      Continuous (fun A : Cfg => χ v A) :=
    p4Q2PV_originalPlaquetteRealCharacter_continuous H v
  have hE (d : Link) :
      Continuous (fun A : Cfg => E ((A d)⁻¹ * B d)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have hObs : Continuous obs :=
    ((hChi p).mul (hChi q)).mul
      (((hE e).mul (hE f)).mul (hE g))
  have hOdd (A : Cfg) : obs (Flip target A) = -obs A := by
    dsimp [obs]
    rw [p4Q2PY3_originalPlaquetteRealCharacter_centerOdd_four
        H p target
          ((p4Q2PY9_originalPlaquettePhysicalEdges_mem H p target).mp hp) A,
      p4Q2PY8_originalPlaquetteChar_centerUnchanged_of_freeEdge
        H q target
          (by
            intro h
            exact hq
              ((p4Q2PY9_originalPlaquettePhysicalEdges_mem H q target).mpr h)) A,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target e he.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target f hf.symm A B,
      p4Q2PU2_originalCrossingEnergy_unchanged_at_other
        H target g hg.symm A B]
    ring
  change (∫ A : Cfg, obs A ∂haar) = 0
  exact p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target obs hObs hOdd

/-- For EVERY pair p ≠ q of actual spatial plaquettes and ANY three
original temporal crossing links, including repetitions, the true
finite-volume SU(2) reference-Haar moment vanishes identically. -/
theorem p4Q2PZ9_originalOffDiagonalPlaquettePair_tripleCrossingHaar_zero
    (p q : Plaq) (hpq : p ≠ q) (e f g : Link) (B : Cfg) :
    (∫ A : Cfg, (χ p A * χ q A) *
      (E ((A e)⁻¹ * B e) *
        E ((A f)⁻¹ * B f) *
        E ((A g)⁻¹ * B g)) ∂haar) = 0 := by
  obtain ⟨target, hside, he, hf, hg⟩ :=
    p4Q2PZ9_originalDistinctPlaquettes_oddFreeLink_for_threeCrossings
      H p q hpq e f g
  have hWard (u v : Plaq) (hu : target ∈ s u) (hv : target ∉ s v) :
      (∫ A : Cfg, (χ u A * χ v A) *
        (E ((A e)⁻¹ * B e) *
          E ((A f)⁻¹ * B f) *
          E ((A g)⁻¹ * B g)) ∂haar) = 0 :=
    p4Q2PZ9_originalPlaquettePair_tripleCrossingHaar_zero_of_freeLink
      H u v e f g target hu hv he hf hg B
  rcases hside with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact hWard p q hp hq
  · calc
      (∫ A : Cfg, (χ p A * χ q A) *
        (E ((A e)⁻¹ * B e) *
          E ((A f)⁻¹ * B f) *
          E ((A g)⁻¹ * B g)) ∂haar) =
        (∫ A : Cfg, (χ q A * χ p A) *
          (E ((A e)⁻¹ * B e) *
            E ((A f)⁻¹ * B f) *
            E ((A g)⁻¹ * B g)) ∂haar) := by
          apply integral_congr_ae
          filter_upwards with A
          ring
      _ = 0 := hWard q p hq hp

end OriginalPairThreeCrossingWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ9_originalDistinctPlaquettes_oddFreeLink_for_threeCrossings
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ9_originalPlaquettePair_tripleCrossingHaar_zero_of_freeLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ9_originalOffDiagonalPlaquettePair_tripleCrossingHaar_zero
