import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorGlobalHilbertFloor
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszExactUnnormalizedTwelveFactor
import Mathlib.Tactic

/-!
# P4-Q2-EA: SHARP structural obstruction in the ACTUAL 6-color link averaging step

DQ compares the genuinely color-normalized independent Haar coordinate
defects with the unnormalized sum of all physical spatial-link coordinate
defects. DZ recovers the exact factor twelve when the original Wilson
Haar 12-color reference average is converted to its UNNORMALIZED sum.

That does NOT remove the averaging by the number of links within each
individual color. In this file we prove an EXACT "if and only if" theorem
for the genuine periodic-even hypercubic spatial LINK CARRIER and its
genuine six color subtypes:

  [forall g : actual links -> ENNReal,
       kappa * sum_all_links g <= sum_colors (1/card color) * sum_color g]
    iff
  [forall color, kappa <= (card actual color links)^(-1)].

The necessity is witnessed by the ACTUAL spatial link selected in each
nonempty color. The sufficient direction is DQ's genuine finite partition
and monotonicity of multiplication of nonnegative extended reals. This
isolates the exact loss of DQ's purely nonnegative per-link averaging
argument; it is not an assumed or proved NO-GO for the genuine Wilson
Riesz spectral gap, because physical Haar fiber defects are constrained
and are not arbitrary nonnegative link weights. New Wilson covariance/
block/locality input would be required to break the universal-weight bound.

No alternate probability law, Wilson/pair-Haar expectation identification,
spatial-volume or spacing-uniform positive coefficient, continuum Hamiltonian, or mass-gap
statement is introduced. No sorry, admit, or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1600000

attribute [local instance] p4Q2BAColorLinksFintype

/-- Canonical honest equivalence between actual six-color link sigma-index
and all genuine periodic-even spatial links. This matches DQ's finite
partition, not a synthetic independent link carrier. -/
private def p4Q2EA_actualSixColorSigmaEquiv (H : ℕ) :
    (Σ c : Fin 6, p4Q2BA_ColorLinks H c) ≃
      PeriodicHypercubicEvenSpatialSliceLink H where
  toFun p := p.2.1
  invFun e :=
    ⟨periodicHypercubicEvenGroundStateSpatialColorEquivFin
        (periodicHypercubicEvenSpatialSliceLinkColor H e),
      ⟨e, by simp⟩⟩
  left_inv := by
    intro p
    rcases p with ⟨c, ⟨e, he⟩⟩
    have hc :
        periodicHypercubicEvenGroundStateSpatialColorEquivFin
          (periodicHypercubicEvenSpatialSliceLinkColor H e) = c := by
      rw [he, Equiv.apply_symm_apply]
    cases hc
    rfl
  right_inv := by
    intro e
    rfl

/-- Actual nonempty color c contributes an actual spatial link e0; the
single-link spike lives on the exact six-color sigma carrier. -/
noncomputable def p4Q2EA_sigmaSpike (H : ℕ)
    (c0 : Fin 6) (e0 : p4Q2BA_ColorLinks H c0) :
    (Σ c : Fin 6, p4Q2BA_ColorLinks H c) → ENNReal :=
  fun p => if p = ⟨c0, e0⟩ then 1 else 0

theorem p4Q2EA_sigmaSpike_sum_one
    (H : ℕ) (c0 : Fin 6) (e0 : p4Q2BA_ColorLinks H c0) :
    (∑ p : (Σ c : Fin 6, p4Q2BA_ColorLinks H c),
      p4Q2EA_sigmaSpike H c0 e0 p) = 1 := by
  classical
  simp [p4Q2EA_sigmaSpike]

/-- The single actual color-spike has weighted six-color sum equal to the
inverse cardinality of the ACTUAL color containing the selected link. -/
theorem p4Q2EA_sigmaSpike_weighted_color_sum
    (H : ℕ) (c0 : Fin 6) (e0 : p4Q2BA_ColorLinks H c0) :
    (∑ c : Fin 6,
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        (∑ e : p4Q2BA_ColorLinks H c,
          p4Q2EA_sigmaSpike H c0 e0 ⟨c, e⟩)) =
      (Fintype.card (p4Q2BA_ColorLinks H c0) : ENNReal)⁻¹ := by
  classical
  have hzero (c : Fin 6) (hc : c ≠ c0) :
      (∑ e : p4Q2BA_ColorLinks H c,
        p4Q2EA_sigmaSpike H c0 e0 ⟨c, e⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro e _he
    have hne :
        (⟨c, e⟩ : Σ d : Fin 6, p4Q2BA_ColorLinks H d) ≠
          ⟨c0, e0⟩ := by
      intro hh
      exact hc (congrArg Sigma.fst hh)
    simp [p4Q2EA_sigmaSpike, hne]
  have hone :
      (∑ e : p4Q2BA_ColorLinks H c0,
        p4Q2EA_sigmaSpike H c0 e0 ⟨c0, e⟩) = 1 := by
    simp [p4Q2EA_sigmaSpike]
  have hsingle :
      (∑ c : Fin 6,
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2EA_sigmaSpike H c0 e0 ⟨c, e⟩)) =
        (Fintype.card (p4Q2BA_ColorLinks H c0) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c0,
            p4Q2EA_sigmaSpike H c0 e0 ⟨c0, e⟩) := by
    apply Finset.sum_eq_single c0
    · intro c _hc hne
      rw [hzero c hne, mul_zero]
    · intro hc
      exact (hc (Finset.mem_univ c0)).elim
  rw [hsingle, hone, mul_one]

/-- The one-coordinate test is transported to the ACTUAL spatial link
carrier using the exact original hypercubic color partition. -/
noncomputable def p4Q2EA_actualLinkSpike
    (H : ℕ) (c0 : Fin 6) (e0 : p4Q2BA_ColorLinks H c0) :
    PeriodicHypercubicEvenSpatialSliceLink H → ENNReal :=
  fun e => p4Q2EA_sigmaSpike H c0 e0
    ((p4Q2EA_actualSixColorSigmaEquiv H).symm e)

theorem p4Q2EA_actualLinkSpike_total_one
    (H : ℕ) (c0 : Fin 6) (e0 : p4Q2BA_ColorLinks H c0) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2EA_actualLinkSpike H c0 e0 e) = 1 := by
  classical
  let E := p4Q2EA_actualSixColorSigmaEquiv H
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        p4Q2EA_actualLinkSpike H c0 e0 e) =
      ∑ p : (Σ c : Fin 6, p4Q2BA_ColorLinks H c),
        p4Q2EA_actualLinkSpike H c0 e0 (E p) :=
      (E.sum_comp (p4Q2EA_actualLinkSpike H c0 e0)).symm
    _ = ∑ p : (Σ c : Fin 6, p4Q2BA_ColorLinks H c),
          p4Q2EA_sigmaSpike H c0 e0 p := by
      apply Finset.sum_congr rfl
      intro p _hp
      change p4Q2EA_sigmaSpike H c0 e0 (E.symm (E p)) =
        p4Q2EA_sigmaSpike H c0 e0 p
      rw [Equiv.symm_apply_apply]
    _ = 1 := p4Q2EA_sigmaSpike_sum_one H c0 e0

theorem p4Q2EA_actualLinkSpike_weighted_color_sum
    (H : ℕ) (c0 : Fin 6) (e0 : p4Q2BA_ColorLinks H c0) :
    (∑ c : Fin 6,
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        (∑ e : p4Q2BA_ColorLinks H c,
          p4Q2EA_actualLinkSpike H c0 e0 e.1)) =
      (Fintype.card (p4Q2BA_ColorLinks H c0) : ENNReal)⁻¹ := by
  classical
  let E := p4Q2EA_actualSixColorSigmaEquiv H
  calc
    (∑ c : Fin 6,
      (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
        (∑ e : p4Q2BA_ColorLinks H c,
          p4Q2EA_actualLinkSpike H c0 e0 e.1)) =
      ∑ c : Fin 6,
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
          (∑ e : p4Q2BA_ColorLinks H c,
            p4Q2EA_sigmaSpike H c0 e0 ⟨c, e⟩) := by
      apply Finset.sum_congr rfl
      intro c _hc
      congr 1
      apply Finset.sum_congr rfl
      intro e _he
      change p4Q2EA_sigmaSpike H c0 e0 (E.symm (E ⟨c, e⟩)) =
        p4Q2EA_sigmaSpike H c0 e0 ⟨c, e⟩
      rw [Equiv.symm_apply_apply]
    _ = _ := p4Q2EA_sigmaSpike_weighted_color_sum H c0 e0

/-- EXACT sharp structural bound: for all possible ENNReal link weights on
the ACTUAL original spatial link carrier, the color-normalized inequality
holds if and only if kappa is bounded above by EACH of the true color
inverse cardinalities. The necessity tests a single ACTUAL spatial link.

This is a theorem about arbitrary nonnegative link data. It does NOT by
itself show that all such weights arise from original Wilson Haar residuals. -/
theorem p4Q2EA_actualColorAverages_lower_coefficient_iff
    (H : ℕ) (κ : ENNReal) :
    (∀ g : PeriodicHypercubicEvenSpatialSliceLink H → ENNReal,
      κ * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, g e) ≤
        ∑ c : Fin 6,
          (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
            (∑ e : p4Q2BA_ColorLinks H c, g e.1)) ↔
    (∀ c : Fin 6,
      κ ≤ (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹) := by
  classical
  constructor
  · intro h c
    let e0 : p4Q2BA_ColorLinks H c :=
      Classical.choice (p4Q2BA_colorLinks_nonempty H c)
    have htest := h (p4Q2EA_actualLinkSpike H c e0)
    rw [p4Q2EA_actualLinkSpike_total_one H c e0,
        p4Q2EA_actualLinkSpike_weighted_color_sum H c e0,
        mul_one] at htest
    exact htest
  · intro h g
    calc
      κ * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, g e) =
          ∑ c : Fin 6,
            κ * (∑ e : p4Q2BA_ColorLinks H c, g e.1) := by
        rw [← p4Q2DQ_sum_colorLinks_eq_allLinks H g, Finset.mul_sum]
      _ ≤ ∑ c : Fin 6,
            (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
              (∑ e : p4Q2BA_ColorLinks H c, g e.1) := by
        apply Finset.sum_le_sum
        intro c _hc
        calc
          κ * (∑ e : p4Q2BA_ColorLinks H c, g e.1) =
              (∑ e : p4Q2BA_ColorLinks H c, g e.1) * κ := mul_comm _ _
          _ ≤ (∑ e : p4Q2BA_ColorLinks H c, g e.1) *
                (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ :=
            mul_le_mul_right (h c) _
          _ = (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal)⁻¹ *
                (∑ e : p4Q2BA_ColorLinks H c, g e.1) := mul_comm _ _

/-- Consequently any universal positive-weight coefficient is no better
than inverse cardinality of a color containing K or more genuine links.
Growing actual color multiplicity alone precludes extracting an H-uniform
constant using only this positive weight inequality. No assertion on
the actual Wilson Riesz spectrum or color-block conditional expectations. -/
theorem p4Q2EA_actualColorAverage_bound_of_color_card
    (H : ℕ) (κ : ENNReal) (c : Fin 6) (K : ℕ)
    (hAvg : ∀ g : PeriodicHypercubicEvenSpatialSliceLink H → ENNReal,
      κ * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, g e) ≤
        ∑ col : Fin 6,
          (Fintype.card (p4Q2BA_ColorLinks H col) : ENNReal)⁻¹ *
            (∑ e : p4Q2BA_ColorLinks H col, g e.1))
    (hK : K ≤ Fintype.card (p4Q2BA_ColorLinks H c)) :
    κ ≤ (K : ENNReal)⁻¹ := by
  have hCoeff :=
    (p4Q2EA_actualColorAverages_lower_coefficient_iff H κ).mp hAvg c
  have hCard :
      (K : ENNReal) ≤
        (Fintype.card (p4Q2BA_ColorLinks H c) : ENNReal) := by
    exact_mod_cast hK
  exact hCoeff.trans (ENNReal.inv_le_inv.mpr hCard)

end

end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EA_actualColorAverages_lower_coefficient_iff
#print axioms MGAP4D.MathlibAnalytic.p4Q2EA_actualColorAverage_bound_of_color_card
