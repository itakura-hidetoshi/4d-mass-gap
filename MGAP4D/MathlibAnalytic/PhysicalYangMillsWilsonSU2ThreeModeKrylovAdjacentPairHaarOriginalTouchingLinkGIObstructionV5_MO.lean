import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalGIMinorTailCauchyV5_MN
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialTargetLinkEnergyVariation
import Mathlib.Tactic

/-!
# P4-Q2-MO — actual spatial Wilson link incidence and GI-density obstruction

MN bounded the signed *original interacting Wilson* compensated spatial
GI minor truncation error by the genuine outside squared minor energy.
MO now uses the actual periodic SU(2) spatial link/plaquette INCIDENCE,
already formalized in the model, rather than an arbitrary geometric core.

For every actual target spatial link e, define the physically grounded
touching core T_H(e) via 4D physical boundary-edge incidence of the
genuine embedded 3D spatial plaquettes. Its proved cardinality is <= 6,
uniformly in the finite periodic spatial extent H.

The genuine Wilson plaquette observable (and the sum of all plaquette
observables outside T_H(e)) is exactly unchanged when the target link
is replaced. The original global spatial Wilson action changes by the
sum of variations of only the <= 6 touching plaquettes, and its
one-link oscillation is at most 12 independent of H. Dividing by the
actual positive plaquette count gives a normalized variation <= 12/N_H.

For the SAME true frozen interacting-Wilson signed GI minor values
d_p = ||T_{H,b}||² Delta_p (no detector, posterior or physical source
is replaced), the actual touching core contributes at most
  sum_(p in T_H(e)) d_p² <= 96 E_b^4,
  |sum_(p in T_H(e)) d_p| <= 24 E_b².
Consequently, for the same original interacting Wilson contexts,
  Q_GI / N_H <= 96 E_b^4 / N_H + Q_outside(T_H(e)) / N_H.
Any proposed extensive uniform GI-square density must therefore
be carried by outside original Wilson minor energy as H increases
at fixed b: the bounded link-touching core alone cannot supply it.

This does NOT say that non-touching ORIGINAL signed posterior GI
responses vanish. Pointwise cylinder-observable locality is NOT
posterior locality; true posterior covariance/receiver sensitivity,
tail decay, positive fine-coupling all-source separation, cross-H
intertwining, H1-C3 and the continuum 4D mass gap all remain OPEN.

Only existing SU(2) Wilson physical geometry, mathlib finite sums,
the true MA bound and MN's real source/detector are used.
No Dobrushin, independent-Haar substitution, artificial rank,
new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2MO_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MO_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MO_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MO_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MO_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Touch" => periodicHypercubicEvenSpatialSliceTouchingPlaquettes H
local notation "W" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "localW" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "n" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "Tail" => p4Q2ML_originalLocalGIOutsideSquareEnergy H b hb

/-- One genuine original local SU(2) Wilson plaquette cylinder observable
is unchanged by replacing a link that does NOT physically touch it. -/
theorem p4Q2MO_originalLocalWilsonObservable_update_eq_of_not_touches
    (A : Cfg) (target : Link) (g : Gauge) (p : Plaq)
    (hp : p ∉ Touch target) :
    localW p (Function.update A target g) = localW p A := by
  have hNotTouches :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target := by
    intro h
    exact hp
      ((periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff
        H target p).2 h)
  have hHolonomy :
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (Function.update A target g) p =
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    ] using
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
        H 2 A target g p hNotTouches)
  change specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (Function.update A target g) p) =
    specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)
  rw [hHolonomy]

/-- The true outside physical cylinder observable sum is pointwise
unchanged when the target SU(2) link is varied, for any H. This
does NOT claim that its interacting posterior expectation is unchanged. -/
theorem p4Q2MO_originalOutsideWilsonObservable_update_eq
    (A : Cfg) (target : Link) (g : Gauge) :
    (∑ p ∈ (Finset.univ : Finset Plaq) \ Touch target,
      localW p (Function.update A target g)) =
    (∑ p ∈ (Finset.univ : Finset Plaq) \ Touch target,
      localW p A) := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  exact p4Q2MO_originalLocalWilsonObservable_update_eq_of_not_touches
    H A target g p (Finset.mem_sdiff.mp hp).2

/-- The link variation of the ACTUAL continuous global spatial Wilson
observable is exactly the finite sum over geometrically touching
plaquettes, not a postulated approximate locality. -/
theorem p4Q2MO_originalWilsonObservable_update_sub_eq_touching
    (A : Cfg) (target : Link) (g : Gauge) :
    W (Function.update A target g) - W A =
      ∑ p ∈ Touch target,
        (localW p (Function.update A target g) - localW p A) := by
  have h :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_update_sub_eq_targetTouching
      H 2 A target g
  exact h

/-- Genuine Wilson spatial-action one-link oscillation is volume
independent even though the whole source sums over O(N_H) plaquettes.
The bound is on the ORIGINAL observable, not the posterior GI map. -/
theorem p4Q2MO_originalWilsonObservable_twoUpdates_abs_le_twelve
    (A : Cfg) (target : Link) (g h : Gauge) :
    |W (Function.update A target g) -
      W (Function.update A target h)| ≤ 12 := by
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuousVacuumReplaceLink_sub_abs_le_twelve
      H 2 (by norm_num) A target g h

/-- Exact positive plaquette-normalization makes the actual Wilson
ONE-LINK observable oscillation at most 12/N_H, without any guessed
covariance decay of an original interacting posterior. -/
theorem p4Q2MO_originalWilsonObservable_normalizedTwoUpdates_abs_le
    (hcount : 0 < n) (A : Cfg) (target : Link) (g h : Gauge) :
    |(W (Function.update A target g) -
      W (Function.update A target h)) / n| ≤ 12 / n := by
  have hOsc :=
    p4Q2MO_originalWilsonObservable_twoUpdates_abs_le_twelve
      H A target g h
  rw [abs_div, abs_of_pos hcount]
  exact (div_le_div_iff_of_pos_right hcount).2 hOsc

/-- For actual interacting-Wilson contexts, the compensated local
GI-minor square energy supported on the <=6 plaquettes touching ONE
physical link is bounded by 96 E_b^4, INDEPENDENT of spatial volume. -/
theorem p4Q2MO_originalTouchingGI_squareEnergy_le_ninetySix
    (target : Link) (e e' : Link) (z z' : Cfg × Cfg) :
    (∑ p ∈ Touch target, (d e e' z z' p)^2) ≤
      96 * E^4 := by
  classical
  have hSum :
      (∑ p ∈ Touch target, (d e e' z z' p)^2) ≤
        ((Touch target).card : ℝ) * (4 * E^2)^2 := by
    have h :=
      Finset.sum_le_card_nsmul (Touch target)
        (fun p : Plaq => (d e e' z z' p)^2)
        ((4 * E^2)^2)
        (fun p hp =>
          p4Q2MA_originalCompensatedLocalGIMinor_sq_le_four_contrastSq_sq
            H b hb e e' z z' p)
    simpa only [nsmul_eq_mul] using h
  have hcard : ((Touch target).card : ℝ) ≤ 6 := by
    exact_mod_cast
      (periodicHypercubicEvenSpatialSliceTouchingPlaquettes_card_le_six H target)
  have hAmp : 0 ≤ (4 * E^2)^2 := sq_nonneg _
  calc
    (∑ p ∈ Touch target, (d e e' z z' p)^2) ≤
      ((Touch target).card : ℝ) * (4 * E^2)^2 := hSum
    _ ≤ 6 * (4 * E^2)^2 :=
      mul_le_mul_of_nonneg_right hcard hAmp
    _ = 96 * E^4 := by ring

/-- In addition, the actual *signed* compensated two-context Wilson
GI minor contribution of all plaquettes touching ONE target link has
absolute value at most 24 E_b², independently of spatial H. -/
theorem p4Q2MO_originalTouchingGI_signedMinor_abs_le_twentyFour
    (target : Link) (e e' : Link) (z z' : Cfg × Cfg) :
    |∑ p ∈ Touch target, d e e' z z' p| ≤ 24 * E^2 := by
  classical
  have hSum :
      (∑ p ∈ Touch target, |d e e' z z' p|) ≤
        ((Touch target).card : ℝ) * (4 * E^2) := by
    have h :=
      Finset.sum_le_card_nsmul (Touch target)
        (fun p : Plaq => |d e e' z z' p|)
        (4 * E^2)
        (fun p hp =>
          p4Q2MA_originalCompensatedLocalGIMinor_abs_le_four_contrastSq
            H b hb e e' z z' p)
    simpa only [nsmul_eq_mul] using h
  have hcard : ((Touch target).card : ℝ) ≤ 6 := by
    exact_mod_cast
      (periodicHypercubicEvenSpatialSliceTouchingPlaquettes_card_le_six H target)
  have hAmp : 0 ≤ 4 * E^2 := by positivity
  calc
    |∑ p ∈ Touch target, d e e' z z' p| ≤
        ∑ p ∈ Touch target, |d e e' z z' p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ((Touch target).card : ℝ) * (4 * E^2) := hSum
    _ ≤ 6 * (4 * E^2) :=
      mul_le_mul_of_nonneg_right hcard hAmp
    _ = 24 * E^2 := by ring

/-- The geometrically link-local fraction of the authentic Wilson GI
square energy cannot exceed 96 E_b⁴/N_H. Only the TRUE outside
interacting-Wilson minor energy can carry any remaining extensive
energy density. -/
theorem p4Q2MO_originalGI_energyDensity_le_touchingPlusOutside
    (hcount : 0 < n) (target : Link)
    (e e' : Link) (z z' : Cfg × Cfg) :
    Q e e' z z' / n ≤
      96 * E^4 / n + Tail e e' z z' (Touch target) / n := by
  have hSplit :=
    p4Q2ML_originalLocalGI_squareEnergy_eq_core_add_outside
      H b hb e e' z z' (Touch target)
  have hCore :=
    p4Q2MO_originalTouchingGI_squareEnergy_le_ninetySix
      H b hb target e e' z z'
  calc
    Q e e' z z' / n =
        ((∑ p ∈ Touch target, (d e e' z z' p)^2) +
          Tail e e' z z' (Touch target)) / n := by rw [hSplit]
    _ ≤ (96 * E^4 + Tail e e' z z' (Touch target)) / n :=
      (div_le_div_iff_of_pos_right hcount).2
        (add_le_add hCore (le_refl _))
    _ = 96 * E^4 / n + Tail e e' z z' (Touch target) / n := by ring

/-- If the genuine original Wilson GI square density has a proposed
positive floor c at one finite volume, its TRUE outside energy must
compensate the explicit volume-diluted <=6-link core. This does NOT
assume or prove c uniformly in H. -/
theorem p4Q2MO_originalGI_densityFloor_requires_outsideLinkEnergy
    (hcount : 0 < n) (target : Link)
    (e e' : Link) (z z' : Cfg × Cfg) (c : ℝ)
    (hc : c ≤ Q e e' z z' / n) :
    c - 96 * E^4 / n ≤
      Tail e e' z z' (Touch target) / n := by
  have h :=
    p4Q2MO_originalGI_energyDensity_le_touchingPlusOutside
      H b hb hcount target e e' z z'
  linarith

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalLocalWilsonObservable_update_eq_of_not_touches
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalOutsideWilsonObservable_update_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalWilsonObservable_update_sub_eq_touching
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalWilsonObservable_twoUpdates_abs_le_twelve
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalWilsonObservable_normalizedTwoUpdates_abs_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalTouchingGI_squareEnergy_le_ninetySix
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalTouchingGI_signedMinor_abs_le_twentyFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalGI_energyDensity_le_touchingPlusOutside
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2MO_originalGI_densityFloor_requires_outsideLinkEnergy
