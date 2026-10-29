import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredPhysicalPlaquetteGlobalHaarCorrelationV5_PZ37ABE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABF — original Wilson full-pair-Haar signed local/residual split

ABE proves EXACTLY that the unchanged original centered Gauss-law Wilson
full GI-gap-square moment G_(H,b,e) is the finite sum of genuine centered
physical plaquette source GLOBAL pair-Haar cross-moments K_(H,b,e,p).
We retain the full signed cross-residual for every chosen actual plaquette:
 R_(H,b,e,p) = SUM_{q != p} K_(H,b,e,q),
 G_(H,b,e) = K_(H,b,e,p) + R_(H,b,e,p).

At every finite H,b>0 ABA2 proves a genuine spatial link with G>0.
A genuine finite original spatial plaquette family has positive cardinality.
The signed average principle then yields one actual plaquette p with
  0 < G_(H,b,e)/|Plaquettes_H| <= K_(H,b,e,p)
and necessarily
  R_(H,b,e,p) <= G_(H,b,e) - G_(H,b,e)/|Plaquettes_H|.

These comparisons have NO absolute value on R and DO NOT assert
nonlocal suppression or volume uniformity. In particular, dividing
by the growing true plaquette count is an EXPLICIT quantitative volume
cost, not a uniform lower bound. The raw K and signed R retain the SAME
original interacting Wilson posterior expectations, original positive
Perron, Gauss-law Hilbert source and full boundary pair-Haar, including
all remote variables. No surrogate Haar conditional measure.

No claim of positive H-independent G, K, all-Hilbert coercivity,
common fine interval, E/F, H1-H4, or continuum mass gap.
No new axioms, sorry/admit/native_decide, legacy JL axioms, Dobrushin.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABF_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABF_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABF_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABF_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABF_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Genuine original residual signed cross-moment, over ALL actual
spatial plaquettes other than the selected physical plaquette.
Each individual K is itself integrated over the COMPLETE original
pair-Haar boundary and uses both interacting Wilson posteriors. -/
noncomputable def p4Q2PZ37ABF_originalSignedFullLocalGlobalCrossResidual
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ :=
  ∑ q ∈ (Finset.univ : Finset
    (PeriodicHypercubicEvenSpatialSlicePlaquette H)).erase p,
    p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e q

/-- Genuine physical full GI second moment decomposes EXACTLY into
the signed full-Haar cross-correlation of one actual physical
plaquette and the entire remaining real signed integral response. -/
theorem p4Q2PZ37ABF_originalFullGIMoment_eq_localCross_add_signedResidual
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e =
      p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p +
        p4Q2PZ37ABF_originalSignedFullLocalGlobalCrossResidual H b hb e p := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let k := p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e
  have hErase := (Finset.univ : Finset Plaq).sum_erase_add k (Finset.mem_univ p)
  have hTotal :
      (∑ q : Plaq, k q) =
        k p + ∑ q ∈ (Finset.univ : Finset Plaq).erase p, k q := by
    simpa only [add_comm] using hErase.symm
  calc
    p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e =
        ∑ q : Plaq, k q :=
      (p4Q2PZ37ABE_originalSum_fullLocalCross_eq_originalFullGIMoment H b hb e).symm
    _ = k p + ∑ q ∈ (Finset.univ : Finset Plaq).erase p, k q := hTotal
    _ = _ := rfl

/-- The true original pair-Haar finite-volume covariance G can be
shared across the original plaquette index. No invented count. -/
private theorem p4Q2PZ37ABF_originalPlaquette_average_sum
    (H : ℕ) (g : ℝ) :
    (∑ _p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      g / (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) = g := by
  classical
  let P : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
  have hPosNat : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
    Fintype.card_pos_iff.mpr ⟨pz37zaSpatialPlaquetteCoordinateFamily H 0⟩
  have hP : P ≠ 0 := by
    apply ne_of_gt
    change (0 : ℝ) < (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
    exact_mod_cast hPosNat
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change P * (g / P) = g
  rw [mul_comm]
  exact div_mul_cancel₀ g hP

/-- A truly QUANTITATIVE local global-Haar signed correlation witness:
at each finite Wilson H,b>0, one real spatial link has strictly
positive original full GI G, and one real physical centered plaquette
captures at least the genuine average G/|Plaquettes_H|. The
growing plaquette count remains explicit and cannot be discarded. -/
theorem p4Q2PZ37ABF_exists_originalLink_plaquette_cross_ge_fullGIMoment_average
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      0 < p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e /
        (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) ∧
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e /
        (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) ≤
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment
            H b hb e p := by
  classical
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  obtain ⟨e, hG⟩ :=
    p4Q2PZ37ABA2_exists_originalLink_positiveUnweightedGIMoment H b hb
  let g : ℝ := p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e
  let P : ℝ := (Fintype.card Plaq : ℝ)
  have hP : 0 < P := by
    have hNat : 0 < Fintype.card Plaq :=
      Fintype.card_pos_iff.mpr ⟨pz37zaSpatialPlaquetteCoordinateFamily H 0⟩
    change (0 : ℝ) < (Fintype.card Plaq : ℝ)
    exact_mod_cast hNat
  have hg : 0 < g := hG
  have hAvg : 0 < g / P := div_pos hg hP
  have hWitness : ∃ p : Plaq,
      g / P ≤
        p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p := by
    by_contra hn
    push Not at hn
    let k := p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e
    have hStrict :
        (∑ p : Plaq, k p) <
          (∑ _p : Plaq, g / P) := by
      apply Finset.sum_lt_sum
      · intro p _hp
        exact (hn p).le
      · let p0 : Plaq := pz37zaSpatialPlaquetteCoordinateFamily H 0
        exact ⟨p0, Finset.mem_univ _, hn p0⟩
    rw [p4Q2PZ37ABE_originalSum_fullLocalCross_eq_originalFullGIMoment,
      p4Q2PZ37ABF_originalPlaquette_average_sum] at hStrict
    exact (lt_irrefl g) hStrict
  obtain ⟨p, hp⟩ := hWitness
  exact ⟨e, p, hAvg, hp⟩

/-- The SAME genuine quantitative witness controls the FULL signed
remaining-plaquette cross integral from ABOVE. Crucially this
residual is signed and may be negative or large in absolute value:
this is NOT a volume-uniform small-tail theorem. -/
theorem p4Q2PZ37ABF_exists_originalQuantitativeCross_and_signedResidual_le
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (p : PeriodicHypercubicEvenSpatialSlicePlaquette H),
      0 < p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e /
        (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) ∧
      p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e /
        (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) ≤
          p4Q2PZ37ABE_originalCenteredFullLocalPhysicalGICrossMoment H b hb e p ∧
      p4Q2PZ37ABF_originalSignedFullLocalGlobalCrossResidual H b hb e p ≤
        p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e -
          p4Q2PZ37AAZ_originalUnweightedCenteredGIGapMoment H b hb e /
            (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  obtain ⟨e, p, hpos, hK⟩ :=
    p4Q2PZ37ABF_exists_originalLink_plaquette_cross_ge_fullGIMoment_average H b hb
  refine ⟨e, p, hpos, hK, ?_⟩
  have hIdentity :=
    p4Q2PZ37ABF_originalFullGIMoment_eq_localCross_add_signedResidual
      H b hb e p
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABF_originalFullGIMoment_eq_localCross_add_signedResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABF_exists_originalLink_plaquette_cross_ge_fullGIMoment_average
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABF_exists_originalQuantitativeCross_and_signedResidual_le
