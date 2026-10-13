import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDensityCancelledLinkEnergyV5_FC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalInputRayleigh
import Mathlib.Tactic

/-!
# P4-Q2-FD: actual Wilson physical Hilbert link localization and two-regime bounds

FC eliminates the artificial ||W||_sup and ||Omega^-1||_sup from TRUE
positive-beta original-Wilson right-link posterior energies. The result
is not inherently restricted to any Krylov family: the genuine
normalized physical receiver and original CondExpL2 link projections
are defined for EVERY physical Haar-L² input.

This file proves:
* one-link exact posterior resampling / pair-Haar squared defect;
* one-link density-cancelled energy and the INDEPENDENT original
  posterior contraction, combined as their minimum for all beta >= 0;
* finite arbitrary physical link patch energy, retaining its REAL links
  without imposing the full spatial volume;
* a precise nonuniform link-profile certificate handoff;
* arbitrary original physical mode-family Gram Rayleigh comparison,
  not assuming orthogonal or linearly independent input modes;
* exact all-physical-input frozen-beta-zero posterior fixedness.

All finite-volume factors and the actual Wilson input norm stay explicit.
No invented posterior, no replacement of the physical joint law by
independent Haar, no Dobrushin, no fabricated spatial decay,
no H/r/n-uniform gap, and no new axiom/sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4Q2FD_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FD_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FD_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FD_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FD_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
private noncomputable instance p4Q2FD_linksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Genuine original-Wilson physical link defect on an ARBITRARY
gauge-invariant physical Haar-L² input, retaining the full
half-density transported ORIGINAL posterior conditional expectation. -/
noncomputable def p4Q2FD_originalPhysicalLinkDefect
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
    pairHaarTransportedGroundStateSpatialLinkProjection
      H N hN beta hbeta e
      (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2

theorem p4Q2FD_originalPhysicalLinkDefect_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e := by
  unfold p4Q2FD_originalPhysicalLinkDefect
  positivity

/-- EXACT ORIGINAL posterior two-copy resampling energy, not an
independent Haar heat bath, equals twice this physical defect. -/
theorem p4Q2FD_originalPhysicalLinkDefect_eq_half_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e =
      (1 / 2 : ℝ) *
        posteriorResamplingEnergy H N hN beta hbeta e
          (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) := by
  have h :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H N hN beta hbeta f e
  change
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) =
    2 * p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e at h
  linarith

/-- The two REAL finite-volume physical bounds are independent:
contraction of the genuine Wilson posterior projection works for
every beta, while FC's density cancellation vanishes at beta=0.
Retain BOTH and take their minimum without claiming volume uniformity. -/
noncomputable def p4Q2FD_originalPhysicalTwoRegimeCoefficient
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  let L := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  min (L ^ 2) ((1 / 2 : ℝ) * L ^ 4 * (Real.exp (8 * beta) ^ 3 - 1) ^ 2)

theorem p4Q2FD_originalPhysicalTwoRegimeCoefficient_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta := by
  unfold p4Q2FD_originalPhysicalTwoRegimeCoefficient
  apply le_min
  · exact sq_nonneg _
  · positivity

/-- An unconditional one-link minimum of the two established TRUE
original-Wilson posterior bounds, for ANY physical input and ANY beta.
The coefficient has no extra factor counting links or Krylov modes. -/
theorem p4Q2FD_originalPhysicalLinkDefect_le_twoRegime
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e ≤
      p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta * ‖f‖ ^ 2 := by
  let L : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let D := p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e
  let E := posteriorResamplingEnergy H N hN beta hbeta e
    (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f)
  have hEq : D = (1 / 2 : ℝ) * E :=
    p4Q2FD_originalPhysicalLinkDefect_eq_half_posterior H N hN beta hbeta f e
  have hBase : E ≤ 2 * (L * ‖f‖) ^ 2 :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le_two_input_sq
      H N hN beta hbeta f e
  have hFC : E ≤ L ^ 4 * (R ^ 3 - 1) ^ 2 * ‖f‖ ^ 2 :=
    p4Q2FC_originalPosteriorResampling_le_densityCancelledSource
      H N hN beta hbeta f e
  have hA : D ≤ L ^ 2 * ‖f‖ ^ 2 := by
    calc
      D = (1 / 2 : ℝ) * E := hEq
      _ ≤ (1 / 2 : ℝ) * (2 * (L * ‖f‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hBase (by norm_num)
      _ = L ^ 2 * ‖f‖ ^ 2 := by ring
  have hB : D ≤ ((1 / 2 : ℝ) * L ^ 4 * (R ^ 3 - 1) ^ 2) * ‖f‖ ^ 2 := by
    calc
      D = (1 / 2 : ℝ) * E := hEq
      _ ≤ (1 / 2 : ℝ) * (L ^ 4 * (R ^ 3 - 1) ^ 2 * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hFC (by norm_num)
      _ = ((1 / 2 : ℝ) * L ^ 4 * (R ^ 3 - 1) ^ 2) * ‖f‖ ^ 2 := by ring
  change D ≤ min (L ^ 2) ((1 / 2 : ℝ) * L ^ 4 * (R ^ 3 - 1) ^ 2) * ‖f‖ ^ 2
  by_cases h : L ^ 2 ≤ (1 / 2 : ℝ) * L ^ 4 * (R ^ 3 - 1) ^ 2
  · simpa only [min_eq_left h] using hA
  · simpa only [min_eq_right (le_of_not_ge h)] using hB

/-- Localize to a literal arbitrary FINITE SUBSET of the genuine
spatial links. The subset may be one edge, one color, a patch, or all
links; no hard-support assumption on the signed source is imposed. -/
noncomputable def p4Q2FD_originalPhysicalRestrictedLinkEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  S.sum (fun e => p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e)

/-- Every physical PATCH has an exact original posterior energy:
the local Wilson conditional fiber loss is not replaced with an
independent measure or a chosen profile. -/
theorem p4Q2FD_originalPhysicalRestrictedLinkEnergy_eq_half_posterior
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S =
      (1 / 2 : ℝ) *
        S.sum (fun e =>
          posteriorResamplingEnergy H N hN beta hbeta e
            (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f)) := by
  unfold p4Q2FD_originalPhysicalRestrictedLinkEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  exact p4Q2FD_originalPhysicalLinkDefect_eq_half_posterior
    H N hN beta hbeta f e

/-- A finite ORIGINAL physical patch is bounded by ITS OWN number
of measured spatial links, not the full 24*(H+1)^3 geometry. -/
theorem p4Q2FD_originalPhysicalRestrictedLinkEnergy_le_card_twoRegime
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S ≤
      (S.card : ℝ) *
        p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta * ‖f‖ ^ 2 := by
  let C := p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta
  have hEach (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e ≤ C * ‖f‖ ^ 2 :=
    p4Q2FD_originalPhysicalLinkDefect_le_twoRegime H N hN beta hbeta f e
  calc
    p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S =
        S.sum (fun e => p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e) := rfl
    _ ≤ S.sum (fun _e => C * ‖f‖ ^ 2) :=
      Finset.sum_le_sum (fun e _he => hEach e)
    _ = (S.card : ℝ) * C * ‖f‖ ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- A mathematically precise LOCAL-PROFILE handoff. To improve the
full-link factor one must prove certified nonuniform b(e) bounds from
genuine Wilson source/conditional geometry. This theorem does not
assert the existence of a spatial decay or a volume-uniform profile. -/
theorem p4Q2FD_originalPhysicalRestrictedLinkEnergy_le_certifiedLinkProfile
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (S : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
    (b : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hb : ∀ e ∈ S,
      p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e ≤
        b e * ‖f‖ ^ 2) :
    p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta f S ≤
      (S.sum b) * ‖f‖ ^ 2 := by
  unfold p4Q2FD_originalPhysicalRestrictedLinkEnergy
  calc
    S.sum (fun e => p4Q2FD_originalPhysicalLinkDefect H N hN beta hbeta f e) ≤
        S.sum (fun e => b e * ‖f‖ ^ 2) :=
      Finset.sum_le_sum (fun e he => hb e he)
    _ = (S.sum b) * ‖f‖ ^ 2 := by rw [Finset.sum_mul]

/-- Real physical source Gram: arbitrary actual physical input family,
not necessarily orthogonal, and no Krylov-order-specific hypothesis.
FC plus the genuine old projection contraction yield a bound in the
TRUE input Hilbert metric rather than coefficient-space ℓ². -/
theorem p4Q2FD_originalWilsonPhysicalGram_rayleigh_le_twoRegime
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H N hN beta hbeta
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta *
      ‖∑ i : ι, a i • f i‖ ^ 2 := by
  classical
  let F := ∑ i : ι, a i • f i
  let L := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  have hExact := pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
    H N hN beta hbeta f a
  have hUpper := p4Q2FD_originalPhysicalRestrictedLinkEnergy_le_card_twoRegime
    H N hN beta hbeta F L
  calc
    star a ⬝ᵥ (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN beta hbeta
          (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) =
        p4Q2FD_originalPhysicalRestrictedLinkEnergy H N hN beta hbeta F L := by
        simpa only [p4Q2FD_originalPhysicalRestrictedLinkEnergy, F, L] using hExact
    _ ≤ (L.card : ℝ) *
        p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta * ‖F‖ ^ 2 :=
      hUpper
    _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        p4Q2FD_originalPhysicalTwoRegimeCoefficient H N hN beta hbeta *
          ‖∑ i : ι, a i • f i‖ ^ 2 := by simp [F, L]

/-- SU(2) physical spatial link cardinality is EXACTLY 24*(H+1)^3.
No artificial coefficient-mode factor is introduced and both true
posterior-bound regimes are retained in a minimum. -/
theorem p4Q2FD_originalWilsonSU2PhysicalGram_rayleigh_le_twoRegime
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H 2 specialUnitaryTwoWilsonRankPositive beta hbeta
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta (f i))) a) ≤
      24 * (H + 1 : ℝ) ^ 3 *
        p4Q2FD_originalPhysicalTwoRegimeCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta *
      ‖∑ i : ι, a i • f i‖ ^ 2 := by
  have h := p4Q2FD_originalWilsonPhysicalGram_rayleigh_le_twoRegime
    H 2 specialUnitaryTwoWilsonRankPositive beta hbeta f a
  rw [p4Q2EU_originalPhysicalSpatialLinks_card_exact H] at h
  push_cast at h
  convert h using 1

/-- The ORIGINAL frozen Wilson beta=0 posterior has exact fixedness
on the full normalized physical receiver RANGE for every input, not
just the previously studied finite Krylov orbit or a chosen source. -/
theorem p4Q2FD_originalWilsonPhysicalReceiver_fixed_beta_zero
    (H N : ℕ) (hN : 0 < N)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (le_refl 0) e
      (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (le_refl 0) f) =
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (le_refl 0) f := by
  let V := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (le_refl 0) f
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (le_refl 0) e
  have hEnergy :=
    p4Q2FD_originalPhysicalLinkDefect_le_twoRegime
      H N hN 0 (le_refl 0) f e
  have hZero : p4Q2FD_originalPhysicalTwoRegimeCoefficient
      H N hN 0 (le_refl 0) = 0 := by
    unfold p4Q2FD_originalPhysicalTwoRegimeCoefficient
    simp
  rw [hZero] at hEnergy
  have hNonneg : 0 ≤ p4Q2FD_originalPhysicalLinkDefect
    H N hN 0 (le_refl 0) f e :=
    p4Q2FD_originalPhysicalLinkDefect_nonneg H N hN 0 (le_refl 0) f e
  have hDefect : p4Q2FD_originalPhysicalLinkDefect
    H N hN 0 (le_refl 0) f e = 0 := by
    have : p4Q2FD_originalPhysicalLinkDefect
      H N hN 0 (le_refl 0) f e ≤ 0 := by
      simpa using hEnergy
    exact le_antisymm this hNonneg
  change ‖V - Q V‖ ^ 2 = 0 at hDefect
  have hNorm : ‖V - Q V‖ = 0 := by
    nlinarith [norm_nonneg (V - Q V)]
  have hV : V - Q V = 0 := norm_eq_zero.mp hNorm
  exact sub_eq_zero.mp hV |>.symm

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalPhysicalLinkDefect_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalPhysicalLinkDefect_eq_half_posterior
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalPhysicalTwoRegimeCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalPhysicalLinkDefect_le_twoRegime
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalPhysicalRestrictedLinkEnergy_eq_half_posterior
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalPhysicalRestrictedLinkEnergy_le_card_twoRegime
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalPhysicalRestrictedLinkEnergy_le_certifiedLinkProfile
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalWilsonPhysicalGram_rayleigh_le_twoRegime
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalWilsonSU2PhysicalGram_rayleigh_le_twoRegime
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FD_originalWilsonPhysicalReceiver_fixed_beta_zero
