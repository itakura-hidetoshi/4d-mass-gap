import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGlobalLocalPhysicalSourceBridgeV5_MM
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# P4-Q2-MN — physical original Wilson GI minor core truncation and exact tail Cauchy bound

MM proved that the original finite-spatial SU(2) Wilson global source
W_H U is the FINITE SUM of the existing gauge-invariant physical
local plaquette sources W_{H,p} U, as vectors in the true Gauss-law
Hilbert space. Its original interacting-posterior GI responses
likewise split into true local signed responses.

This module quantifies the resulting truncation error of the ORIGINAL
transfer-compensated two-context GI minor (not a surrogate receiver,
rank detector, independently sampled Haar law, or source plane):

  D = ||T||² Δ_global = Σ_p d_p,     Q_outside(S) = Σ_{p∉S} d_p².

For any actual finite plaquette subset S, at the SAME positive/zero
frozen coupling and SAME original interacting Wilson contexts,

  D - Σ_{p∈S}d_p = Σ_{p∉S}d_p,
  (D - Σ_{p∈S}d_p)² ≤ |P_H \ S| Q_outside(S).

If N_H > 0, the precisely normalized version is

  ((D - Σ_{p∈S}d_p)/N_H)²
    ≤ (|P_H \ S|/N_H) (Q_outside(S)/N_H).

The inequality uses pinned mathlib's finite-set Cauchy-Schwarz
sq_sum_le_card_mul_sum_sq, not an assumed physical tail decay.
Crucially, the exact *signed* truncation difference is ALSO expressed
through actual two-interacting-posterior physical GI responses of the
Gauss-law unit U and genuine local Wilson Hilbert vectors W_{H,p}U.
The transfer compensation is only the previously proved positive
scalar ||T||²; no posterior is replaced.

This bounds a genuinely physical spatial GI MINOR localization error;
it does NOT bound each individual signed channel's far-field tail
without a separate analytic argument, prove uniform source
coercivity, or intertwine the fine positive-coupling Krylov endpoint.
H1-C1/C2/C3 and the 4D continuum Yang–Mills gap remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "D" => p4Q2LW_originalCompensatedSpatialGIMinor H b hb
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "Tail" => p4Q2ML_originalLocalGIOutsideSquareEnergy H b hb
local notation "tN" => p4Q2LW_originalPhysicalTransferNorm H b hb
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "W" => p4Q2JU_originalSpatialWilsonPhysicalSource H
local notation "Wp" => p4Q2LO_originalLocalPlaquettePhysicalSource H
local notation "GI" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

/-- The compensated original global two-context Wilson GI minor
is EXACTLY the determinant of TWO actual signed interacting-posterior
responses evaluated on the true Gauss-law unit and global Wilson
physical source. The only compensation is the exact ||T||² scalar. -/
theorem p4Q2MN_originalCompensatedGlobalMinor_eq_physicalResponses
    (e e' : Link) (z z' : Cfg × Cfg) :
    D e e' z z' =
      tN^2 *
        (GI b hb U e z * GI b hb W e' z' -
         GI b hb W e z * GI b hb U e' z') := by
  rw [p4Q2LW_originalCompensatedSpatialGIMinor_eq_sq_mul_original]
  unfold p4Q2JI_originalGISpatialActionMinor
  rw [p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI H b hb e z,
      p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI H b hb e' z',
      p4Q2JU_originalSpatialWilsonGI_eq_actualPhysicalGI H b hb e z,
      p4Q2JU_originalSpatialWilsonGI_eq_actualPhysicalGI H b hb e' z']

/-- The *same original* compensated local minor is the physical
two-posterior determinant of unit and actual p-dependent Wilson
Gauss-law source. Neither row is a substituted Haar conditional. -/
theorem p4Q2MN_originalCompensatedLocalMinor_eq_physicalResponses
    (e e' : Link) (z z' : Cfg × Cfg) (p : Plaq) :
    d e e' z z' p =
      tN^2 *
        (GI b hb U e z * GI b hb (Wp p) e' z' -
         GI b hb (Wp p) e z * GI b hb U e' z') := by
  rw [p4Q2LW_originalCompensatedLocalGIMinor_eq_sq_mul_original]
  unfold p4Q2LO_originalLocalPlaquetteGIMinor
  rw [p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI H b hb e z,
      p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI H b hb e' z',
      p4Q2LO_originalLocalPlaquetteGI_eq_physicalGI H b hb e z p,
      p4Q2LO_originalLocalPlaquetteGI_eq_physicalGI H b hb e' z' p]

/-- Original global compensated two-context GI minor minus its
restriction to any actual plaquette core equals the exact SIGNED
sum of the genuine original local GI minors on the complement. -/
theorem p4Q2MN_originalCompensatedGI_globalMinusCore_eq_outside
    (e e' : Link) (z z' : Cfg × Cfg) (S : Finset Plaq) :
    D e e' z z' - (∑ p ∈ S, d e e' z z' p) =
      ∑ p ∈ (Finset.univ : Finset Plaq) \ S, d e e' z z' p := by
  classical
  rw [p4Q2LY_originalCompensatedGlobalMinor_eq_sum_local]
  have hsplit :=
    Finset.sum_sdiff
      (s₁ := S) (s₂ := (Finset.univ : Finset Plaq))
      (f := fun p : Plaq => d e e' z z' p)
      (Finset.subset_univ S)
  have hsum :
      (∑ p : Plaq, d e e' z z' p) =
        (∑ p ∈ S, d e e' z z' p) +
        (∑ p ∈ (Finset.univ : Finset Plaq) \ S, d e e' z z' p) := by
    calc
      (∑ p : Plaq, d e e' z z' p) =
          (∑ p ∈ (Finset.univ : Finset Plaq) \ S, d e e' z z' p) +
          (∑ p ∈ S, d e e' z z' p) := hsplit.symm
      _ = (∑ p ∈ S, d e e' z z' p) +
          (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
            d e e' z z' p) := add_comm _ _
  rw [hsum]
  ring

/-- The signed original Wilson GI truncation error is literally a
TWO-INTERACTING-POSTERIOR physical response determinant made from the
actual outside Gauss-law local source contributions. Nothing is
assumed about the size of either physical signed tail. -/
theorem p4Q2MN_originalCompensatedGI_coreError_eq_physicalOutside
    (e e' : Link) (z z' : Cfg × Cfg) (S : Finset Plaq) :
    D e e' z z' - (∑ p ∈ S, d e e' z z' p) =
      tN^2 *
        (GI b hb U e z *
          (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
            GI b hb (Wp p) e' z') -
         (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
            GI b hb (Wp p) e z) *
          GI b hb U e' z') := by
  classical
  rw [p4Q2MN_originalCompensatedGI_globalMinusCore_eq_outside]
  have hSum :
      (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
          d e e' z z' p) =
        ∑ p ∈ (Finset.univ : Finset Plaq) \ S,
          tN^2 *
            (GI b hb U e z * GI b hb (Wp p) e' z' -
              GI b hb (Wp p) e z * GI b hb U e' z') := by
    apply Finset.sum_congr rfl
    intro p hp
    exact p4Q2MN_originalCompensatedLocalMinor_eq_physicalResponses
      H b hb e e' z z' p
  rw [hSum, ← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Pinned mathlib Cauchy–Schwarz on the ACTUAL outside plaquette
subset, with real original compensated local GI minors and literally
their previously defined genuine physical Q_outside, not a new energy. -/
theorem p4Q2MN_originalCompensatedGI_outside_sum_sq_le_card_tailEnergy
    (e e' : Link) (z z' : Cfg × Cfg) (S : Finset Plaq) :
    (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
      d e e' z z' p)^2 ≤
      (((Finset.univ : Finset Plaq) \ S).card : ℝ) *
        Tail e e' z z' S := by
  classical
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Plaq) \ S)
    (f := fun p : Plaq => d e e' z z' p)
  simpa only [p4Q2ML_originalLocalGIOutsideSquareEnergy] using hCS

/-- Exact ORIGINAL global-to-core physical GI minor truncation
error has a squared upper bound by actual outside cardinality
times the genuine original local GI squared tail. -/
theorem p4Q2MN_originalCompensatedGI_coreError_sq_le_card_tailEnergy
    (e e' : Link) (z z' : Cfg × Cfg) (S : Finset Plaq) :
    (D e e' z z' - (∑ p ∈ S, d e e' z z' p))^2 ≤
      (((Finset.univ : Finset Plaq) \ S).card : ℝ) *
        Tail e e' z z' S := by
  rw [p4Q2MN_originalCompensatedGI_globalMinusCore_eq_outside]
  exact p4Q2MN_originalCompensatedGI_outside_sum_sq_le_card_tailEnergy
    H b hb e e' z z' S

/-- The precise N_H-normalized ORIGINAL Wilson signed-minor
localization error bound. The RHS is outside plaquette FRACTION
times the actual original compensated GI square-ENERGY DENSITY
outside S. Uniform decay of this product remains UNPROVEN. -/
theorem p4Q2MN_originalCompensatedGI_normalizedCoreError_sq_le_tailDensity
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg)
    (S : Finset Plaq) :
    ((D e e' z z' - (∑ p ∈ S, d e e' z z' p)) / n)^2 ≤
      ((((Finset.univ : Finset Plaq) \ S).card : ℝ) / n) *
        (Tail e e' z z' S / n) := by
  have hSq : 0 < n^2 := sq_pos_of_pos hcount
  have hTail :=
    p4Q2MN_originalCompensatedGI_coreError_sq_le_card_tailEnergy
      H b hb e e' z z' S
  calc
    ((D e e' z z' - (∑ p ∈ S, d e e' z z' p)) / n)^2 =
        (D e e' z z' - (∑ p ∈ S, d e e' z z' p))^2 / n^2 := by ring
    _ ≤ ((((Finset.univ : Finset Plaq) \ S).card : ℝ) *
          Tail e e' z z' S) / n^2 :=
      (div_le_div_iff_of_pos_right hSq).2 hTail
    _ = ((((Finset.univ : Finset Plaq) \ S).card : ℝ) / n) *
        (Tail e e' z z' S / n) := by ring

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MN_originalCompensatedGlobalMinor_eq_physicalResponses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MN_originalCompensatedLocalMinor_eq_physicalResponses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MN_originalCompensatedGI_globalMinusCore_eq_outside
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MN_originalCompensatedGI_coreError_eq_physicalOutside
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MN_originalCompensatedGI_outside_sum_sq_le_card_tailEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MN_originalCompensatedGI_coreError_sq_le_card_tailEnergy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MN_originalCompensatedGI_normalizedCoreError_sq_le_tailDensity
