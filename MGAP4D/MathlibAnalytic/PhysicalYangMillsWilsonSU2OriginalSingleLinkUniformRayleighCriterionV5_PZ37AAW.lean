import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullMeanActiveDirectionV5_PZ37AAV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAW — true Wilson single-link criterion for volume-uniform Rayleigh

AAT/AAU established UNCONDITIONAL spatial translation covariance of the
original two genuine interacting Wilson conditional posterior laws, their
Gauss-law centered GI response, and original FX variance. AAP consequently
gives, for EVERY actual positive spatial link e of every finite volume,

  j_(H,b,e) ≤ 3 R_(H,b) / |Links_H|.

This file extracts a new quantitative SUFFICIENCY criterion:
ONE original link e per volume with j_e ≥ 3 c / |Links_H| already forces
the full actual centered physical Wilson Rayleigh R_(H,b) ≥ c. The
previously proved AAK pigeonhole theorem supplies the converse NECESSARY
witness with factor one whenever R_(H,b) ≥ c.

We formulate these implications both for a single finite H and for an
arbitrary volume-dependent positive coupling family b(H). Hence the
volume-uniform Rayleigh problem is reduced (up to the SHARP THREE original
spatial-direction orbit factor) to a single truly interacting Wilson link
posterior response witness per volume, not a bound on all links.

No assertion that the requisite uniform single-link witness EXISTS.
No volume-uniform coercivity or common fine interval is claimed, no new
E/F, H1–H4 or continuum Yang–Mills mass gap. The original SU(2) kernel,
physical Gauss-law source, interacting posterior and Haar are unchanged.
Append-only, no axioms/sorry/admit/native_decide or new assumptions hidden.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAW_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAW_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAW_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAW_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAW_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAW_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section ActualOneLinkCriterion
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "j" =>
  p4Q2PZ37AAK_originalNormalizedLinkResponse H
local notation "R" =>
  p4Q2PZ37AAH_originalExactCenteredRayleighFloor H

/-- The exact full original Wilson Rayleigh floor always supplies at
least one genuine original spatial-link posterior witness at the
corresponding 1/|Links_H| scale. This implication is unconditional. -/
theorem p4Q2PZ37AAW_originalSingleLinkNecessary_of_RayleighFloor
    (b : ℝ) (hb : 0 < b) (c : ℝ)
    (hFloor : c ≤ R b hb) :
    ∃ e : Link,
      c / (Fintype.card Link : ℝ) ≤ j b hb e := by
  exact p4Q2PZ37AAK_exists_link_ge_average_of_Rayleigh_floor
    H b hb c hFloor

/-- Crucial reverse implication: because all actual spatial
translations are already proved to preserve the SAME original
interacting Wilson posterior response, ONE witness with THREE times the
target scaled mean forces the complete physical Rayleigh floor. -/
theorem p4Q2PZ37AAW_originalRayleighFloor_of_tripleScaledSingleLink
    (b : ℝ) (hb : 0 < b) (c : ℝ)
    (hWitness : ∃ e : Link,
      (3 * c) / (Fintype.card Link : ℝ) ≤ j b hb e) :
    c ≤ R b hb := by
  obtain ⟨e, he⟩ := hWitness
  have hL : (0 : ℝ) < (Fintype.card Link : ℝ) :=
    p4Q2PZ37AAK_originalLinkCount_pos H
  have hCap : j b hb e ≤ (3 * R b hb) / (Fintype.card Link : ℝ) :=
    p4Q2PZ37AAP_covariance_implies_originalRelativeLinkCap
      H b hb
      (p4Q2PZ37AAU_originalPosteriorSpatialTranslationCovariant H b hb) e
  have hThree : 3 * c ≤ 3 * R b hb :=
    (div_le_div_iff_of_pos_right hL).mp (he.trans hCap)
  linarith only [hThree]

end ActualOneLinkCriterion

/-- All-volume NECESSARY witness for any actual positive fine
coupling family and any proposed volume-independent Rayleigh floor.
The source-normalized original Wilson link count is retained. -/
theorem p4Q2PZ37AAW_allVolumes_singleLinkNecessary
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H) (c : ℝ)
    (hRayleigh : ∀ H,
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H)) :
    ∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      c / (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H (b H) (hb H) e := by
  intro H
  exact p4Q2PZ37AAW_originalSingleLinkNecessary_of_RayleighFloor
    H (b H) (hb H) c (hRayleigh H)

/-- A VOLUME-UNIFORM ORIGINAL POSITIVE PHYSICAL RAYLEIGH FLOOR is
mathematically implied by ONE uniformly scaled authentic posterior
witness PER volume. The link-witness hypothesis is explicit and is
NOT asserted unconditionally. This is a sharpened reduction of the
remaining true Wilson coercivity problem, not its solution. -/
theorem p4Q2PZ37AAW_allVolumes_uniformRayleigh_of_singleLinkWitness
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H) (c : ℝ) (hc : 0 < c)
    (hWitness : ∀ H,
      ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (3 * c) /
            (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) ≤
          p4Q2PZ37AAK_originalNormalizedLinkResponse H (b H) (hb H) e) :
    0 < c ∧ ∀ H,
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  refine ⟨hc, ?_⟩
  intro H
  exact p4Q2PZ37AAW_originalRayleighFloor_of_tripleScaledSingleLink
    H (b H) (hb H) c (hWitness H)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAW_originalSingleLinkNecessary_of_RayleighFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAW_originalRayleighFloor_of_tripleScaledSingleLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAW_allVolumes_singleLinkNecessary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAW_allVolumes_uniformRayleigh_of_singleLinkWitness
