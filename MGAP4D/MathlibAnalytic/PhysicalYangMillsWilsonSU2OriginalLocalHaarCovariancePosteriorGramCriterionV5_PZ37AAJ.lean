import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHaarPosteriorPlaquetteNormalizedFloorV5_PZ37AAI
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAJ — exact local Haar covariance / true posterior Gram criterion

The original Gauss-law centered physical Wilson source V_H is represented
by one half of the sum of the REAL original centered local Wilson
plaquette Haar-L2 vectors, as kernel-checked in PZ37AAI. We expand its
physical Hilbert squared norm EXACTLY into a double sum of original
product-Haar centered plaquette inner products.

The ORIGINAL four-link support and product-Haar independence proofs
in PZ37AAI remove EVERY cross term with disjoint actual link supports.
Thus the *exact* physical source norm is one quarter of a genuinely
finite-local overlap covariance sum, not an extensive proxy.

For every finite H and positive frozen b, the unchanged original
TWO interacting Wilson posteriors, all spatial links and all boundary
pair-Haar variables give a true GL Gram G_(H,b). The exact criterion

  c <= R_(H,b)(V_H)  iff  (c/4) * HaarCov_H <= G_(H,b)

is both NECESSARY and SUFFICIENT for each H, and likewise for arbitrary
volume-indexed frozen couplings b_H. This sharpens the earlier AAI
sufficient condition m_(H,b)>=24*c*P_H, which can be far stronger than
the actually needed physical source-relative Gram inequality.

No posterior is replaced by Haar. No unconditional volume-uniform
positive c, common fine interval, E/F, H1-H4, or continuum Yang-Mills
mass gap is asserted. No new axiom, sorry/admit/native_decide,
or change to previous theorem carriers.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAJ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAJ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAJ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAJ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAJ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- The original centered product-Haar covariance summed over every
pair of ACTUAL spatial plaquettes. It is a reference Haar quantity
only, NOT a substitute for either interacting Wilson posterior. -/
noncomputable def p4Q2PZ37AAJ_originalHaarPlaquetteCovariance (H : ℕ) : ℝ :=
  ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
    ∑ q : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      inner ℝ (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p)
        (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H q)

/-- Bilinearity identifies the exact Haar covariance with the square
of the ORIGINAL all-plaquette centered Haar synthesis norm. -/
theorem p4Q2PZ37AAJ_originalHaarSynthesis_norm_sq_eq_covariance (H : ℕ) :
    ‖p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis H
      (fun _ => (1 : ℝ))‖^2 =
      p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H := by
  classical
  unfold p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis
    p4Q2PZ37AAJ_originalHaarPlaquetteCovariance
  simp only [one_smul]
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  rw [Finset.sum_comm]

/-- True product-Haar covariance has EXACT finite four-link locality:
every pair with disjoint original link supports contributes zero. -/
theorem p4Q2PZ37AAJ_originalHaarCovariance_eq_actualLocalOverlap (H : ℕ) :
    p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        ∑ q ∈ pz37zaSpatialPlaquetteOverlap H p,
          inner ℝ (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p)
            (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H q) := by
  classical
  unfold p4Q2PZ37AAJ_originalHaarPlaquetteCovariance
  apply Finset.sum_congr rfl
  intro p _hp
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _hq hnot
  exact p4Q2PZ37AAI_centeredPlaquette_inner_zero_of_disjoint H p q
    (pz37zaSpatialPlaquetteSupport_disjoint_of_not_overlap H p q hnot)

/-- The *original* Gauss-law Hilbert norm, without changing the
physical carrier or vacuum, is EXACTLY one quarter of the finite-local
product-Haar covariance of the genuine Wilson plaquette family. -/
theorem p4Q2PZ37AAJ_originalPhysicalNorm_sq_eq_quarterHaarCovariance (H : ℕ) :
    ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 =
      (1 / 4 : ℝ) * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H := by
  let S := p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis H (fun _ => 1)
  have hEq :
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖ =
        ‖(1 / 2 : ℝ) • S‖ := by
    change ‖(p4Q2PZ37ZW_originalCenteredPhysicalDirection H :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))‖ =
        ‖(1 / 2 : ℝ) • S‖
    exact congrArg norm
      (p4Q2PZ37AAI_originalCenteredPhysicalFormula_coe_eq_halfHaarSynthesis H)
  have hSq :
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 =
        (1 / 4 : ℝ) * ‖S‖^2 := by
    rw [hEq, norm_smul, Real.norm_eq_abs]
    norm_num [mul_pow]
  calc
    ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 =
      (1 / 4 : ℝ) * ‖S‖^2 := hSq
    _ = (1 / 4 : ℝ) * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H := by
      rw [p4Q2PZ37AAJ_originalHaarSynthesis_norm_sq_eq_covariance H]

/-- The exact local original Haar covariance is STRICTLY positive
because the unchanged centered physical Wilson action is nonconstant. -/
theorem p4Q2PZ37AAJ_originalHaarCovariance_pos (H : ℕ) :
    0 < p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H := by
  have hNorm :
      0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
    pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
  have hEq := p4Q2PZ37AAJ_originalPhysicalNorm_sq_eq_quarterHaarCovariance H
  linarith

/-- Original Haar covariance has the rigorously proved volume-local
24-Bessel UPPER bound; this is not a posterior GL lower bound. -/
theorem p4Q2PZ37AAJ_originalHaarCovariance_le_twentyFourPlaquetteCount (H : ℕ) :
    p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H ≤
      24 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  have h := p4Q2PZ37AAI_originalCenteredHaarPlaquetteUnitSum_sq_le_card H
  rw [p4Q2PZ37AAJ_originalHaarSynthesis_norm_sq_eq_covariance H] at h
  exact h

/-- The EXACT equivalence of a true posterior-centered Rayleigh
lower floor and the ORIGINAL product-Haar finite-local covariance
versus the unchanged two-posterior GL Gram. This removes the coarse
AAI plaquette-count envelope entirely from the logical criterion. -/
theorem p4Q2PZ37AAJ_originalRayleighFloor_iff_posteriorGram_ge_localHaarCovariance
    (H : ℕ) (b : ℝ) (hb : 0 < b) (c : ℝ) :
    (c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb) ↔
      (c / 4) * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb := by
  have hNorm :
      0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
    pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
  have hFactor :
      c * ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 =
        (c / 4) * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H := by
    rw [p4Q2PZ37AAJ_originalPhysicalNorm_sq_eq_quarterHaarCovariance H]
    ring
  unfold p4Q2PZ37AAH_originalExactCenteredRayleighFloor
  rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
  rw [le_div_iff₀ hNorm, hFactor]

/-- For EVERY arbitrary volume-dependent positive frozen original
Wilson coupling b_H, a shared fine-ZERO positive physical Rayleigh
floor c is equivalent to a genuinely local Haar-covariance-relative
interacting-posterior GL Gram lower comparison. Neither direction
asserts existence of such c or uniform positive-fine convergence. -/
theorem p4Q2PZ37AAJ_uniformFineZeroRayleigh_iff_localHaarPosteriorGram
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H) (c : ℝ) :
    (∀ H : ℕ,
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H)) ↔
    (∀ H : ℕ,
      (c / 4) * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H)) := by
  constructor
  · intro h H
    exact (p4Q2PZ37AAJ_originalRayleighFloor_iff_posteriorGram_ge_localHaarCovariance
      H (b H) (hb H) c).mp (h H)
  · intro h H
    exact (p4Q2PZ37AAJ_originalRayleighFloor_iff_posteriorGram_ge_localHaarCovariance
      H (b H) (hb H) c).mpr (h H)

/-- A positive all-volume fine-ZERO floor exists if and only if
one positive multiple of the ACTUAL local Haar covariance is
dominated by the ACTUAL original interacting-posterior Gram at
every volume. This is a sharpened equivalent obstruction, not its
discharge. -/
theorem p4Q2PZ37AAJ_existsUniformPositiveFineZero_iff_localCovariancePosteriorFrame
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H) :
    (∃ c : ℝ, 0 < c ∧ ∀ H : ℕ,
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H)) ↔
    (∃ c : ℝ, 0 < c ∧ ∀ H : ℕ,
      (c / 4) * p4Q2PZ37AAJ_originalHaarPlaquetteCovariance H ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H)) := by
  constructor
  · rintro ⟨c, hc, hAll⟩
    exact ⟨c, hc,
      (p4Q2PZ37AAJ_uniformFineZeroRayleigh_iff_localHaarPosteriorGram
        b hb c).mp hAll⟩
  · rintro ⟨c, hc, hAll⟩
    exact ⟨c, hc,
      (p4Q2PZ37AAJ_uniformFineZeroRayleigh_iff_localHaarPosteriorGram
        b hb c).mpr hAll⟩

/-- The same necessary-and-sufficient all-volume criterion written
EXPLICITLY as a sum only over actual four-link-overlapping spatial
plaquettes. Independent disjoint supports contribute no hidden term. -/
theorem p4Q2PZ37AAJ_uniformFineZeroRayleigh_iff_overlapCovariancePosteriorGram
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H) (c : ℝ) :
    (∀ H : ℕ,
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H)) ↔
    (∀ H : ℕ,
      (c / 4) * (∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        ∑ q ∈ pz37zaSpatialPlaquetteOverlap H p,
          inner ℝ (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p)
            (p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H q)) ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H)) := by
  simpa only [p4Q2PZ37AAJ_originalHaarCovariance_eq_actualLocalOverlap] using
    (p4Q2PZ37AAJ_uniformFineZeroRayleigh_iff_localHaarPosteriorGram b hb c)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_originalHaarSynthesis_norm_sq_eq_covariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_originalHaarCovariance_eq_actualLocalOverlap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_originalPhysicalNorm_sq_eq_quarterHaarCovariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_originalHaarCovariance_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_originalHaarCovariance_le_twentyFourPlaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_originalRayleighFloor_iff_posteriorGram_ge_localHaarCovariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_uniformFineZeroRayleigh_iff_localHaarPosteriorGram
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_existsUniformPositiveFineZero_iff_localCovariancePosteriorFrame
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAJ_uniformFineZeroRayleigh_iff_overlapCovariancePosteriorGram
