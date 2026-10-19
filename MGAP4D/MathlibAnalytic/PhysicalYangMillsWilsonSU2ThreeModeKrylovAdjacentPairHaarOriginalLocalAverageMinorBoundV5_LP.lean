import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalPlaquetteGIWitnessV5_LO
import Mathlib.Tactic

/-!
# P4-Q2-LP — original Wilson local minor has an explicit plaquette-count floor

LO proves that the TRUE interacting-Wilson-posterior two-context GI minor
of the ORIGINAL complete spatial Wilson action is exactly the finite sum
of the GI minors of all original local SU(2) plaquette energies.
LM proves this total minor nonzero at two genuine boundary contexts for
any finite H and b > 0.

Using the mathlib finite-set maximum of absolute minor values, together
with the triangle inequality on a real finite list, prove that one actual
spatial plaquette satisfies

  |Δ_local| >= |Δ_total| / (number of original spatial plaquettes).

The count is the actual canonical plaquette-list length; NOT a synthetic
volume surrogate. In particular both this local minor and the exact
positive Frobenius coercivity coefficient from LO are nonzero.

This is a finite-volume quantitative geometric selection result only:
no bound on the H-dependence of the global minor, detector normalizers,
or resulting physical Hilbert coercivity coefficient is claimed.
No artificial rank, independent Haar posterior, Dobrushin or new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- Triangle inequality for a finite REAL list when every summand
absolute value is bounded by the same explicit number. -/
private theorem p4Q2LP_abs_list_sum_le_len_mul_of_bound
    {α : Type*} (f : α → ℝ) (B : ℝ) :
    ∀ xs : List α, (∀ p ∈ xs, |f p| ≤ B) →
      |(xs.map f).sum| ≤ (xs.length : ℝ) * B := by
  intro xs
  induction xs with
  | nil => simp
  | cons p xs ih =>
      intro hB
      have hp : |f p| ≤ B := hB p (by simp)
      have htail : ∀ q ∈ xs, |f q| ≤ B := by
        intro q hq
        exact hB q (by simp [hq])
      have hxs := ih htail
      calc
        |((p :: xs).map f).sum| = |f p + (xs.map f).sum| := by simp
        _ ≤ |f p| + |(xs.map f).sum| := abs_add_le _ _
        _ ≤ B + (xs.length : ℝ) * B := add_le_add hp hxs
        _ = ((p :: xs).length : ℝ) * B := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Finite-max witness with the sharp cardinality factor:
nonzero REAL finite-list sum implies an actual list element whose
absolute value is at least the average absolute total. -/
private theorem p4Q2LP_exists_averaged_list_witness
    {α : Type*} (xs : List α) (f : α → ℝ)
    (hsum : (xs.map f).sum ≠ 0) :
    ∃ p ∈ xs, 0 < (xs.length : ℝ) ∧ 0 < |f p| ∧
      |(xs.map f).sum| / (xs.length : ℝ) ≤ |f p| := by
  classical
  cases xs with
  | nil => simp at hsum
  | cons a rest =>
      obtain ⟨p, hp, hmax⟩ :=
        Finset.exists_max_image ((a :: rest).toFinset)
          (fun q => |f q|) ⟨a, by simp⟩
      have hpList : p ∈ a :: rest := by simpa using hp
      have hBound : ∀ q ∈ a :: rest, |f q| ≤ |f p| := by
        intro q hq
        exact hmax q (by simpa using hq)
      have hTriangle :=
        p4Q2LP_abs_list_sum_le_len_mul_of_bound f |f p|
          (a :: rest) hBound
      have hn : 0 < ((a :: rest).length : ℝ) := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        positivity
      have hsumpos : 0 < |((a :: rest).map f).sum| :=
        abs_pos.mpr hsum
      have hpPos : 0 < |f p| := by
        by_contra hNot
        have hpZero : |f p| = 0 :=
          le_antisymm (le_of_not_gt hNot) (abs_nonneg _)
        rw [hpZero, mul_zero] at hTriangle
        linarith
      refine ⟨p, hpList, hn, hpPos, ?_⟩
      exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using hTriangle)

end GroundStatePosteriorJoint

local instance p4Q2LP_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LP_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LP_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LP_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LP_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H

/-- The actual number of original modern spatial-slice SU(2) plaquettes,
computed from the SAME canonical finite list that defines Wilson action. -/
noncomputable def p4Q2LP_originalSpatialPlaquetteCount : ℕ :=
  (periodicHypercubicEvenSpatialSlicePlaquetteList H).length

/-- LM and LO, sharpened: for every finite H, beta>0 and pair of actual
links, some genuine pair of original interacting Wilson boundary contexts
and one ACTUAL original spatial plaquette give a quantitatively large
local minor, at least the total Wilson minor divided by the REAL
number of spatial plaquettes. -/
theorem p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
      0 < |p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z' p| ∧
      |p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z'| /
          (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
        |p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z' p| := by
  obtain ⟨z, z', hTotal⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
      H b hb e e' left₀ right₀
  have hSum :
      (((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p =>
        p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z' p).sum) ≠ 0 := by
    rw [← p4Q2LO_originalSpatialGIMinor_eq_sum_local H b hb.le e e' z z']
    exact hTotal
  obtain ⟨p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_exists_averaged_list_witness
      (periodicHypercubicEvenSpatialSlicePlaquetteList H)
      (p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z') hSum
  refine ⟨z, z', p, hp, ?_, hpPos, ?_⟩
  · simpa only [p4Q2LP_originalSpatialPlaquetteCount] using hn
  · rw [p4Q2LO_originalSpatialGIMinor_eq_sum_local]
    simpa only [p4Q2LP_originalSpatialPlaquetteCount] using hAvg

/-- The SAME quantitative local-plaquette witness is a TRUE physical
Gauss-law two-source detector: the physical vectors are constant-unit
and multiplication by the selected original plaquette energy.
The positive Frobenius coefficient is supplied by LO/LN, and the new
geometric minor floor holds simultaneously at these EXACT contexts. -/
theorem p4Q2LP_originalLocalPhysicalGI_exists_averaged_coercive
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg, ∃ p : Plaq,
      p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H ∧
      ∃ κ : ℝ,
        0 < κ ∧
        0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ∧
        |p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z'| /
            (p4Q2LP_originalSpatialPlaquetteCount H : ℝ) ≤
          |p4Q2LO_originalLocalPlaquetteGIMinor H b hb.le e e' z z' p| ∧
        ∀ x y : ℝ,
          κ * (x^2 + y^2) ≤
            (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
              H b hb.le (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e z)^2 +
            (p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
              H b hb.le (p4Q2LO_originalPhysicalLocalTwoSource H p x y) e' z')^2 := by
  obtain ⟨z, z', p, hp, hn, hpPos, hAvg⟩ :=
    p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
      H b hb e e' left₀ right₀
  have hLocal : p4Q2LO_originalLocalPlaquetteGIMinor
      H b hb.le e e' z z' p ≠ 0 := by
    intro hz
    simp [hz] at hpPos
  obtain ⟨hκ, hbound⟩ :=
    p4Q2LO_originalPhysicalLocalTwoSourceGI_explicit_coercive
      H b hb.le e e' z z' p hLocal
  exact ⟨z, z', p, hp,
    p4Q2LO_originalLocalGIQuantitativeCoefficient
      H b hb.le e e' z z' p,
    hκ, hn, hAvg, hbound⟩

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LP_originalLocalPlaquetteMinor_exists_averaged
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LP_originalLocalPhysicalGI_exists_averaged_coercive