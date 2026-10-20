import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMeanEnergySinglePlaquetteV5_MK
import Mathlib.Tactic

/-!
# P4-Q2-ML — authentic original Wilson GI spatial core/tail and contrast obstruction

LM–MK prove a true nonzero finite-volume original interacting Wilson
two-context GI minor, genuine local plaquette square energy Q, and a
physical coercivity lower certificate proportional to Q/N.

Here we split THAT SAME original compensated local GI square energy over
ANY subset S of the ACTUAL finite SU(2) spatial plaquette carrier.
The outside term is literally the sum of genuine original local minor
squares over the remaining original plaquettes; it is not a detector,
measure, posterior, or hypothetical independent-Haar replacement.

Using MA's already PROVED pointwise original Wilson bound
   DeltaBar_p^2 <= (4 E_b^2)^2 = 16 E_b^4,
we obtain the exact/quantitative spatial obstruction
   Q/N <= (|S|/N) 16 E_b^4 + Q_outside(S)/N.

Thus any proposed volume-uniform original GI energy-density floor
requires either an extensive genuinely responsive core or sufficient
genuine far-field square energy. A small relative core AND a small
normalized outside tail force density dilution. This is a conditional
necessary implication, NOT a proof of either actual Wilson tail decay
or a volume-uniform lower bound.

Separately, the very same LY–MK lower certificate k=(Q/N)/(10 E_b^2)
always obeys 0 <= k <= (8/5) E_b^2 for positive b. Therefore the
particular certificate cannot be uniformly positive along schedules
with E_{b_n}->0, although this does NOT bound the TRUE physical
coercivity coefficient from above.

All results hold for the unchanged original interacting Wilson
posterior and true Gauss-law physical source definitions imported
from MK/MA, with no new physical assumption, artificial rank,
Dobrushin, sorry, admit or axiom. Positive fine-coupling arbitrary-depth
source separation and H1-C3 remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2ML_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2ML_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2ML_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2ML_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2ML_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb

/-- The actual original Wilson local GI square energy OUTSIDE a finite
subset S of the genuine original spatial plaquettes. This is a restricted
sum of the existing physical minor values, not another GI detector. -/
noncomputable def p4Q2ML_originalLocalGIOutsideSquareEnergy
    (e e' : Link) (z z' : Cfg × Cfg) (S : Finset Plaq) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset Plaq) \ S, (d e e' z z' p)^2

local notation "Tail" => p4Q2ML_originalLocalGIOutsideSquareEnergy H b hb

/-- Exact genuine Wilson spatial core/outside splitting. The original
compensated physical local GI minor is NEVER replaced or changed. -/
theorem p4Q2ML_originalLocalGI_squareEnergy_eq_core_add_outside
    (e e' : Link) (z z' : Cfg × Cfg) (S : Finset Plaq) :
    Q e e' z z' =
      (∑ p ∈ S, (d e e' z z' p)^2) + Tail e e' z z' S := by
  classical
  change (∑ p : Plaq, (d e e' z z' p)^2) =
    (∑ p ∈ S, (d e e' z z' p)^2) +
      (∑ p ∈ (Finset.univ : Finset Plaq) \ S, (d e e' z z' p)^2)
  have hsplit :=
    Finset.sum_sdiff
      (s₁ := S) (s₂ := (Finset.univ : Finset Plaq))
      (f := fun p : Plaq => (d e e' z z' p)^2)
      (Finset.subset_univ S)
  calc
    (∑ p : Plaq, (d e e' z z' p)^2) =
        (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
          (d e e' z z' p)^2) +
        (∑ p ∈ S, (d e e' z z' p)^2) := hsplit.symm
    _ = (∑ p ∈ S, (d e e' z z' p)^2) +
          (∑ p ∈ (Finset.univ : Finset Plaq) \ S,
            (d e e' z z' p)^2) := add_comm _ _

/-- MA's genuine original local Wilson amplitude bound controls the
core contribution by its ACTUAL cardinality, with the genuine outside
energy left untouched. No spatial clustering is assumed. -/
theorem p4Q2ML_originalLocalGI_squareEnergy_core_tail_upper
    (e e' : Link) (z z' : Cfg × Cfg) (S : Finset Plaq) :
    Q e e' z z' ≤
      (S.card : ℝ) * (4 * E^2)^2 + Tail e e' z z' S := by
  classical
  have hcore :
      (∑ p ∈ S, (d e e' z z' p)^2) ≤
        (S.card : ℝ) * (4 * E^2)^2 := by
    have hfinite :=
      Finset.sum_le_card_nsmul S
        (fun p : Plaq => (d e e' z z' p)^2)
        ((4 * E^2)^2)
        (fun p hp =>
          p4Q2MA_originalCompensatedLocalGIMinor_sq_le_four_contrastSq_sq
            H b hb e e' z z' p)
    simpa only [nsmul_eq_mul] using hfinite
  calc
    Q e e' z z' =
        (∑ p ∈ S, (d e e' z z' p)^2) +
          Tail e e' z z' S :=
      p4Q2ML_originalLocalGI_squareEnergy_eq_core_add_outside
        H b hb e e' z z' S
    _ ≤ (S.card : ℝ) * (4 * E^2)^2 +
          Tail e e' z z' S := add_le_add_right hcore _

/-- Exact finite-H localized-core/physical-tail obstruction:
  Q/N <= (|S|/N) 16 E_b^4 + outsideEnergy(S)/N.
This holds on original Wilson plaquettes for all genuine contexts,
without any tail hypothesis. -/
theorem p4Q2ML_originalLocalGI_energyDensity_core_tail_upper
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg)
    (S : Finset Plaq) :
    Q e e' z z' / n ≤
      ((S.card : ℝ) / n) * (16 * E^4) +
        Tail e e' z z' S / n := by
  calc
    Q e e' z z' / n ≤
        ((S.card : ℝ) * (4 * E^2)^2 +
          Tail e e' z z' S) / n :=
      (div_le_div_iff_of_pos_right hcount).2
        (p4Q2ML_originalLocalGI_squareEnergy_core_tail_upper
          H b hb e e' z z' S)
    _ = ((S.card : ℝ) / n) * (16 * E^4) +
          Tail e e' z z' S / n := by ring

/-- A prescribed positive extensive GI density is possible ONLY if
the actual original far-field contribution compensates any small
genuinely responsive core. This theorem introduces no density claim:
the assumed c-floor is explicitly an unproved external premise when
one attempts an H-uniform application. -/
theorem p4Q2ML_originalLocalGI_density_requires_outside_energy
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg)
    (S : Finset Plaq) (c : ℝ)
    (hc : c ≤ Q e e' z z' / n) :
    c - ((S.card : ℝ) / n) * (16 * E^4) ≤
      Tail e e' z z' S / n := by
  have hupper :=
    p4Q2ML_originalLocalGI_energyDensity_core_tail_upper
      H b hb hcount e e' z z' S
  linarith

/-- A subextensive core fraction together with a small normalized
authentic outside GI energy forces a small GI density. This is the
specific real Wilson localization/dilution obstruction for U0, NOT
a claim that Wilson receivers actually satisfy either hypothesis. -/
theorem p4Q2ML_originalLocalGI_density_le_of_core_and_tail_bounds
    (hcount : 0 < n) (e e' : Link) (z z' : Cfg × Cfg)
    (S : Finset Plaq) (eps tailBound : ℝ)
    (hcore : ((S.card : ℝ) / n) ≤ eps)
    (htail : Tail e e' z z' S / n ≤ tailBound) :
    Q e e' z z' / n ≤ eps * (16 * E^4) + tailBound := by
  have hupper :=
    p4Q2ML_originalLocalGI_energyDensity_core_tail_upper
      H b hb hcount e e' z z' S
  have hamp : 0 ≤ 16 * E^4 := by positivity
  calc
    Q e e' z z' / n ≤
        ((S.card : ℝ) / n) * (16 * E^4) +
          Tail e e' z z' S / n := hupper
    _ ≤ eps * (16 * E^4) + tailBound :=
      add_le_add
        (mul_le_mul_of_nonneg_right hcore hamp) htail

/-- The SPECIFIC ORIGINAL Wilson LY–MK certificate k=(Q/N)/(10E²)
has a genuine, unconditional contrast ceiling (8/5) E². This is NOT
an upper bound on the actual local physical coercivity kappa.
It isolates a necessary coupling-schedule check before H1-C3. -/
theorem p4Q2ML_originalGI_linearCertificate_contrast_ceiling
    (hpos : 0 < b) (hcount : 0 < n)
    (e e' : Link) (z z' : Cfg × Cfg) :
    0 ≤ (Q e e' z z' / n) / (10 * E^2) ∧
      (Q e e' z z' / n) / (10 * E^2) ≤
        (8 / 5 : ℝ) * E^2 := by
  have hE : 0 < E :=
    p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hDen : 0 < 10 * E^2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hE)
  have hQ : 0 ≤ Q e e' z z' :=
    p4Q2LY_originalCompensatedLocalGISquareEnergy_nonneg
      H b hb e e' z z'
  constructor
  · exact div_nonneg (div_nonneg hQ hcount.le) hDen.le
  · calc
      (Q e e' z z' / n) / (10 * E^2) ≤
          (16 * E^4) / (10 * E^2) :=
        (div_le_div_iff_of_pos_right hDen).2
          (p4Q2MA_originalCompensatedLocalGISquareEnergy_density_le_sixteen
            H b hb hcount e e' z z')
      _ = (8 / 5 : ℝ) * E^2 := by
        apply (div_eq_iff hDen.ne').2
        ring

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ML_originalLocalGI_squareEnergy_eq_core_add_outside
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ML_originalLocalGI_squareEnergy_core_tail_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ML_originalLocalGI_energyDensity_core_tail_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ML_originalLocalGI_density_requires_outside_energy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ML_originalLocalGI_density_le_of_core_and_tail_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2ML_originalGI_linearCertificate_contrast_ceiling
