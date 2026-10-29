import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorSignalProbeV5_PZ37AAX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAX2 — local raw Wilson posterior mass suffices uniformly

The original time-zero Wilson spatial lattice has precisely three true
positive spatial-link directions and three true spatial plaquette planes
at every vertex. Consequently its genuine link and plaquette counts
are EQUAL, including the smallest even-periodic volume.

AAJ gives the exact original centered Haar source covariance upper bound
C_H <= 24 * genuine spatial plaquette count. Therefore C_H <= 24*L_H,
where L_H is the genuine spatial LINK count. Combining this UNCONDITIONAL
source-scale comparison with AAW's true Wilson one-link criterion yields:

  one ORIGINAL unnormalized pair-Haar GI/FX posterior link integral
  J_(H,b,e) >= epsilon  implies  R_(H,b)(V_H) >= epsilon/18.

This identifies a more physical, volume-free single-link analytic
obligation: prove a constant positive lower bound for ONE actual raw
two-interacting-Wilson-posterior gap-square/FX-variance integral per H.
The existence of such a common epsilon is NOT asserted here.
No Haar posterior replacement, no changed physical Gauss-law source,
no new axioms/sorry/admit/native_decide, coercivity, common fine
interval, endpoints E/F, H1--H4, or continuum mass gap. Append-only.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AAX2_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAX2_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAX2_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAX2_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAX2_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAX2_vertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) :=
  Fintype.ofFinite _
private noncomputable instance p4Q2PZ37AAX2_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact combinatorial identity on the ORIGINAL periodic spatial Wilson
lattice, not a synthetic graph: three true positive spatial links and
three ordered spatial plaquette planes per time-zero base vertex. -/
theorem p4Q2PZ37AAX2_originalPlaquetteCount_eq_linkCount (H : ℕ) :
    Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) =
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  have hD : Fintype.card PeriodicHypercubicEvenSpatialDirection = 3 :=
    p4Q2PZ37AAP_originalSpatialDirection_card_three
  have hP : Fintype.card PeriodicHypercubicEvenSpatialDirectionPair = 3 := by
    decide
  let V := PeriodicHypercubicEvenSpatialSliceVertex H
  let P := PeriodicHypercubicEvenSpatialDirectionPair
  let D := PeriodicHypercubicEvenSpatialDirection
  have hUnivP :
      (Finset.univ : Finset (V × P)) =
        (Finset.univ : Finset V).product (Finset.univ : Finset P) := by
    ext x
    simp
  have hUnivD :
      (Finset.univ : Finset (V × D)) =
        (Finset.univ : Finset V).product (Finset.univ : Finset D) := by
    ext x
    simp
  have hCardP :
      Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) =
        Fintype.card V * Fintype.card P := by
    calc
      Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) =
          (Finset.univ : Finset (V × P)).card := by simp
      _ = ((Finset.univ : Finset V).product (Finset.univ : Finset P)).card := by
        rw [hUnivP]
      _ = (Finset.univ : Finset V).card * (Finset.univ : Finset P).card := by
        rw [Finset.product_eq_sprod, Finset.card_product]
      _ = Fintype.card V * Fintype.card P := by simp
  have hCardD :
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) =
        Fintype.card V * Fintype.card D := by
    calc
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) =
          (Finset.univ : Finset (V × D)).card := by simp
      _ = ((Finset.univ : Finset V).product (Finset.univ : Finset D)).card := by
        rw [hUnivD]
      _ = (Finset.univ : Finset V).card * (Finset.univ : Finset D).card := by
        rw [Finset.product_eq_sprod, Finset.card_product]
      _ = Fintype.card V * Fintype.card D := by simp
  calc
    Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) =
        Fintype.card V * Fintype.card P := hCardP
    _ = Fintype.card V * Fintype.card D := by rw [hP, hD]
    _ = Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := hCardD.symm

/-- The SAME exact centered Haar covariance of the genuine physical
Wilson source is at most 24 times the number of ORIGINAL spatial links.
This is ONLY a source-normalization bound, never a replacement for the
two interacting posterior measures. -/
theorem p4Q2PZ37AAX2_originalHaarCovariance_le_twentyFourLinks (H : ℕ) :
    p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H ≤
      24 * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) := by
  have h :=
    p4Q2PZ37AAJ_originalHaarCovariance_le_twentyFourPlaquetteCount H
  rw [p4Q2PZ37AAX2_originalPlaquetteCount_eq_linkCount H] at h
  exact h

/-- A single *RAW*, volume-independent genuine two-posterior Wilson
GI/FX pair-Haar response epsilon immediately suffices for a genuine
physical centered Rayleigh epsilon/18 lower bound. Nothing assumes the
relative Rayleigh itself: only one original non-normalized link integral
appears in the premise. The raw witness existence is NOT proved. -/
theorem p4Q2PZ37AAX2_originalRayleighFloor_of_rawSingleLink
    (H : ℕ) (b : ℝ) (hb : 0 < b) (epsilon : ℝ) (heps : 0 ≤ epsilon)
    (hRaw : ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      epsilon ≤ p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e) :
    epsilon / 18 ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  obtain ⟨e, he⟩ := hRaw
  let C : ℝ := p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let J : ℝ := p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H b hb e
  have hC : 0 < C := p4Q2PZ37AAJ_originalHaarCovariance_pos H
  have hL : 0 < L := p4Q2PZ37AAK_originalLinkCount_pos H
  have hCcap : C ≤ 24 * L :=
    p4Q2PZ37AAX2_originalHaarCovariance_le_twentyFourLinks H
  have hScaled : epsilon * C ≤ 24 * J * L := by
    calc
      epsilon * C ≤ epsilon * (24 * L) :=
        mul_le_mul_of_nonneg_left hCcap heps
      _ ≤ J * (24 * L) := by
        apply mul_le_mul_of_nonneg_right he
        positivity
      _ = 24 * J * L := by ring
  have hBound : epsilon / (6 * L) ≤ (4 * J) / C := by
    apply (div_le_div_iff₀ (by positivity : 0 < (6 : ℝ) * L) hC).mpr
    nlinarith only [hScaled]
  have hWitness :
      (3 * (epsilon / 18)) / L ≤
        p4Q2PZ37AAK_originalNormalizedLinkResponse H b hb e := by
    change (3 * (epsilon / 18)) / L ≤ (4 * J) / C
    convert hBound using 1
    ring
  exact p4Q2PZ37AAW_originalRayleighFloor_of_tripleScaledSingleLink
    H b hb (epsilon / 18) ⟨e, hWitness⟩

/-- For arbitrary volume-dependent positive original Wilson frozen
couplings, a common strictly positive RAW one-link posterior response
would give a common strictly positive fine-zero physical Rayleigh floor.
The premise is a genuine unsolved microscopic lower bound. -/
theorem p4Q2PZ37AAX2_allVolumes_uniformRayleigh_of_rawSingleLink
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (epsilon : ℝ) (heps : 0 < epsilon)
    (hRaw : ∀ H, ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      epsilon ≤ p4Q2PZ37AAK_originalCenteredLinkPosteriorResponse H (b H) (hb H) e) :
    0 < epsilon / 18 ∧ ∀ H,
      epsilon / 18 ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  refine ⟨by positivity, ?_⟩
  intro H
  exact p4Q2PZ37AAX2_originalRayleighFloor_of_rawSingleLink
    H (b H) (hb H) epsilon heps.le (hRaw H)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX2_originalPlaquetteCount_eq_linkCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX2_originalHaarCovariance_le_twentyFourLinks
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX2_originalRayleighFloor_of_rawSingleLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAX2_allVolumes_uniformRayleigh_of_rawSingleLink