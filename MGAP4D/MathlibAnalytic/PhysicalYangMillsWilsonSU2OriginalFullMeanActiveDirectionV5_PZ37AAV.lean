import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnconditionalPosteriorParticipationV5_PZ37AAU3
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAV — full-Rayleigh-mean active direction on the original Wilson lattice

AAU discharged the genuine GI/FX posterior spatial-translation obstruction and
proved that each ORIGINAL spatial-direction fiber carries constant source-
normalized two-interacting-Wilson-posterior response. All original links are
partitioned into precisely three full translation orbits, one per direction.

A generic second-moment argument yielded the earlier 1/12 density at the
HALF-Rayleigh mean threshold. The ORIGINAL exact link sum plus the complete
direction orbits yields a strictly stronger statement without any estimate:
at least one WHOLE positive spatial-direction orbit has every original link
above the FULL exact centered physical Rayleigh-mean response R/|Links|.
Consequently at least 1/3 of ALL original spatial links are active at the
full mean threshold (not merely half the mean).

This is exact fixed-H,b>0 Wilson posterior geometry with genuine Gauss-law
source and original GI/FX conditional posteriors. It is NOT a uniform
positive-in-volume Rayleigh floor, coercivity or a common positive fine
interval, endpoint E/F, H1–H4, or continuum 4D Yang–Mills mass gap.
No model replacement, new axiom, sorry/admit/native_decide; append-only.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAV_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAV_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAV_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAV_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAV_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAV_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
private noncomputable instance p4Q2PZ37AAV_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section OriginalFullMeanOrbit
variable (H : ℕ)
local notation "V" => PeriodicHypercubicEvenSpatialSliceVertex H
local notation "D" => PeriodicHypercubicEvenSpatialDirection
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "j" =>
  p4Q2PZ37AAK_originalNormalizedLinkResponse H
local notation "R" =>
  p4Q2PZ37AAH_originalExactCenteredRayleighFloor H

/-- A whole genuine original spatial direction lies ABOVE the full
actual centered physical Wilson Rayleigh mean R/|Links|, not merely the
half-mean used in the earlier second-moment estimate. This is an
unconditional consequence of AAU and original exact link-sum geometry. -/
theorem p4Q2PZ37AAV_originalExists_fullMeanActiveDirection
    (b : ℝ) (hb : 0 < b) :
    ∃ d : D, ∀ v : V,
      R b hb / (Fintype.card Link : ℝ) ≤ j b hb (v,d) := by
  have hCov :=
    p4Q2PZ37AAU_originalPosteriorSpatialTranslationCovariant H b hb
  have hHom :
      ∀ e f : Link, e.2 = f.2 → j b hb e = j b hb f :=
    p4Q2PZ37AAP_originalNormalizedLink_directionHomogeneous
      H b hb hCov
  obtain ⟨e, he⟩ :=
    p4Q2PZ37AAK_exists_link_ge_average_of_Rayleigh_floor
      H b hb (R b hb) (le_refl (R b hb))
  refine ⟨e.2, ?_⟩
  intro v
  calc
    R b hb / (Fintype.card Link : ℝ) ≤ j b hb e := he
    _ = j b hb (v,e.2) := hHom e (v,e.2) rfl

/-- Every link of a full genuine spatial orbit meets the exact mean
threshold. The original vertex-to-link coordinate injection is used,
not a synthetic index set. -/
theorem p4Q2PZ37AAV_originalExists_fullActiveOrbit
    (b : ℝ) (hb : 0 < b) :
    ∃ d : D,
      ((Finset.univ : Finset V).image
        (fun v : V => ((v,d) : Link))) ⊆
      p4Q2PZ37AAL_originalActiveLinks H b hb (R b hb) := by
  obtain ⟨d, hd⟩ :=
    p4Q2PZ37AAV_originalExists_fullMeanActiveDirection H b hb
  refine ⟨d, ?_⟩
  intro e he
  rcases Finset.mem_image.mp he with ⟨v, _hv, rfl⟩
  exact (p4Q2PZ37AAL_mem_originalActiveLinks_iff
    H b hb (R b hb) (v,d)).mpr (hd v)

/-- Unlike generic Paley-Zygmund, the ORIGINAL three-translation-orbit
structure guarantees at least ONE THIRD of all original links at the
FULL Rayleigh average threshold, for every H and b>0 unconditionally. -/
theorem p4Q2PZ37AAV_originalFullMeanActiveDensity_ge_oneThird
    (b : ℝ) (hb : 0 < b) :
    ((1 / 3 : ℝ) * (Fintype.card Link : ℝ)) ≤
      ((p4Q2PZ37AAL_originalActiveLinks H b hb
        (R b hb)).card : ℝ) := by
  classical
  obtain ⟨d, hd⟩ :=
    p4Q2PZ37AAV_originalExists_fullActiveOrbit H b hb
  let S : Finset Link :=
    (Finset.univ : Finset V).image (fun v : V => ((v,d) : Link))
  have hInjective :
      Function.Injective (fun v : V => ((v,d) : Link)) := by
    intro v w hvw
    exact congrArg Prod.fst hvw
  have hS : S.card = Fintype.card V := by
    change ((Finset.univ : Finset V).image
      (fun v : V => ((v,d) : Link))).card = Fintype.card V
    rw [Finset.card_image_of_injective (Finset.univ : Finset V) hInjective]
    simp
  have hSsub : S ⊆
      p4Q2PZ37AAL_originalActiveLinks H b hb (R b hb) := hd
  have hCount : Fintype.card Link = 3 * Fintype.card V := by
    change Fintype.card (V × D) = 3 * Fintype.card V
    rw [Fintype.card_prod, p4Q2PZ37AAP_originalSpatialDirection_card_three]
    omega
  have hCountReal :
      (Fintype.card Link : ℝ) = 3 * (Fintype.card V : ℝ) := by
    exact_mod_cast hCount
  calc
    (1 / 3 : ℝ) * (Fintype.card Link : ℝ) =
        (Fintype.card V : ℝ) := by
      rw [hCountReal]
      ring
    _ = (S.card : ℝ) := by exact_mod_cast hS.symm
    _ ≤ ((p4Q2PZ37AAL_originalActiveLinks H b hb
      (R b hb)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSsub

end OriginalFullMeanOrbit
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAV_originalExists_fullMeanActiveDirection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAV_originalExists_fullActiveOrbit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAV_originalFullMeanActiveDensity_ge_oneThird
