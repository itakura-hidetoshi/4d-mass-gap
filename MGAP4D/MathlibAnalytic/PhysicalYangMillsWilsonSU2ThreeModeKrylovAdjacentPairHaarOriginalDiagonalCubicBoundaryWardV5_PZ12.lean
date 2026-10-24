import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDiagonalOddTripleTraceV5_PZ11
import Mathlib.Tactic

/-!
# P4-Q2-PZ12 — genuine SU(2) diagonal cubic-crossing Ward invariance

For the ORIGINAL spatial Haar and unchanged complete temporal Wilson
crossing, the original squared spatial plaquette character chi_p^2
has a boundary-independent weighted third crossing moment.

Write E_e = 1 - tau_e. The exact polynomial identity for E_e E_f E_g
is the sum of its three E-pairs minus its three E-singletons plus 1
minus tau_e tau_f tau_g. The *genuine* PZ11 center-even/odd-trace
Ward theorem annihilates the last term, the original PY7C one-trace
Ward fixes the singletons, and the original PY8 pair Haar invariance
fixes ALL pairs, with repeated indices. No substitute posterior.

PZ10's full ordered-crossing-cube expansion and off-diagonal
plaquette-pair cancellation then give diagonal and centered-square
cubic-crossing invariance in all original finite even volumes,
including the period-two case.

These are ORIGINAL Haar identities, not a claim of universal W6
cancellation, a nonzero three-mode witness, U0 or mass gap.
No new axiom, sorry/admit, Dobrushin or fabricated kernel.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ12_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ12_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ12_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ12_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ12_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ12_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirection
local instance p4Q2PZ12_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section OriginalDiagonalCubicWard

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "χ" => p4Q2PV_originalPlaquetteRealCharacter H
local notation "Φ" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H

/-- Every genuine ordered triple of original temporal SU(2) link
energies has a right-boundary invariant chi_p^2-weighted Haar moment.
NO assumptions of pairwise distinct links or factorized laws. -/
theorem p4Q2PZ12_originalPlaquetteSquare_threeCrossingLinkHaar_invariant
    (p : Plaq) (e f g : Link) (B : Cfg) :
    (∫ X : Cfg, (χ p X)^2 *
      (E ((X e)⁻¹ * B e) * E ((X f)⁻¹ * B f) *
        E ((X g)⁻¹ * B g)) ∂haar) =
    (∫ X : Cfg, (χ p X)^2 *
      (E ((X e)⁻¹) * E ((X f)⁻¹) *
        E ((X g)⁻¹)) ∂haar) := by
  let I : Cfg := fun _ => 1
  let w : Cfg → ℝ := fun X => (χ p X)^2
  let u : Cfg → Link → Cfg → ℝ :=
    fun D d X => E ((X d)⁻¹ * D d)
  let t1 : Cfg → Link → Cfg → ℝ :=
    fun D d X => w X * u D d X
  let t2 : Cfg → Link → Link → Cfg → ℝ :=
    fun D d k X => w X * (u D d X * u D k X)
  let t3 : Cfg → Cfg → ℝ :=
    fun D X => w X * (u D e X * u D f X * u D g X)
  let residue : Cfg → Cfg → ℝ :=
    fun D X => w X *
      ((1 - u D e X) * (1 - u D f X) * (1 - u D g X))
  let pairs : Cfg → Cfg → ℝ :=
    fun D X => t2 D e f X + t2 D e g X + t2 D f g X
  let singles : Cfg → Cfg → ℝ :=
    fun D X => t1 D e X + t1 D f X + t1 D g X
  let reduced : Cfg → Cfg → ℝ :=
    fun D X => pairs D X - singles D X + w X
  have hw : Continuous w :=
    (p4Q2PV_originalPlaquetteRealCharacter_continuous H p).pow 2
  have hu (D : Cfg) (d : Link) : Continuous (u D d) := by
    change Continuous (fun X : Cfg => E ((X d)⁻¹ * D d))
    exact (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply d).inv.mul continuous_const)
  have ht1 (D : Cfg) (d : Link) :
      Continuous (t1 D d) := hw.mul (hu D d)
  have ht2 (D : Cfg) (d k : Link) :
      Continuous (t2 D d k) := hw.mul ((hu D d).mul (hu D k))
  have ht3 (D : Cfg) :
      Continuous (t3 D) :=
    hw.mul (((hu D e).mul (hu D f)).mul (hu D g))
  have hresidue (D : Cfg) : Continuous (residue D) :=
    hw.mul
      (((continuous_const.sub (hu D e)).mul
        (continuous_const.sub (hu D f))).mul
          (continuous_const.sub (hu D g)))
  have hpairs (D : Cfg) : Continuous (pairs D) :=
    ((ht2 D e f).add (ht2 D e g)).add (ht2 D f g)
  have hsingles (D : Cfg) : Continuous (singles D) :=
    ((ht1 D e).add (ht1 D f)).add (ht1 D g)
  have hred (D : Cfg) : Continuous (reduced D) :=
    ((hpairs D).sub (hsingles D)).add hw
  have hiw : Integrable w haar :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 (D : Cfg) (d : Link) : Integrable (t1 D d) haar :=
    (ht1 D d).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 (D : Cfg) (d k : Link) : Integrable (t2 D d k) haar :=
    (ht2 D d k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hOne (D : Cfg) (d : Link) :
      (∫ X : Cfg, t1 D d X ∂haar) = (∫ X : Cfg, w X ∂haar) := by
    have hiTrace : Integrable
        (fun X : Cfg => w X * (1 - u D d X)) haar :=
      (hw.mul (continuous_const.sub (hu D d))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hZero :
        (∫ X : Cfg, w X * (1 - u D d X) ∂haar) = 0 := by
      exact p4Q2PY7_originalPlaquetteSquare_oneTemporalTrace_Haar_zero
        H p d D
    have hPoint (X : Cfg) :
        t1 D d X = w X - w X * (1 - u D d X) := by
      dsimp [t1]
      ring
    calc
      (∫ X : Cfg, t1 D d X ∂haar) =
        ∫ X : Cfg, w X - w X * (1 - u D d X) ∂haar := by
          apply integral_congr_ae
          filter_upwards with X
          exact hPoint X
      _ = (∫ X : Cfg, w X ∂haar) -
          (∫ X : Cfg, w X * (1 - u D d X) ∂haar) := by
          simpa only [Pi.sub_apply] using (integral_sub hiw hiTrace)
      _ = (∫ X : Cfg, w X ∂haar) := by rw [hZero, sub_zero]
  have hPair (D : Cfg) (d k : Link) :
      (∫ X : Cfg, t2 D d k X ∂haar) =
        (∫ X : Cfg, t2 I d k X ∂haar) := by
    simpa only [t2, w, u, I, Pi.one_apply, mul_one] using
      (p4Q2PY8_originalPlaquetteSquare_crossingPairHaar_invariant
        H p d k D)
  have hTripleZero (D : Cfg) :
      (∫ X : Cfg, residue D X ∂haar) = 0 := by
    exact p4Q2PZ11_originalPlaquetteSquare_threeTemporalTracesHaar_zero
      H p e f g D
  have hMoment (D : Cfg) :
      (∫ X : Cfg, t3 D X ∂haar) =
        (∫ X : Cfg, reduced D X ∂haar) := by
    have hPoint (X : Cfg) :
        t3 D X = reduced D X - residue D X := by
      dsimp [t3, reduced, pairs, singles, t2, t1, residue]
      ring
    calc
      (∫ X : Cfg, t3 D X ∂haar) =
          ∫ X : Cfg, reduced D X - residue D X ∂haar := by
            apply integral_congr_ae
            filter_upwards with X
            exact hPoint X
      _ = (∫ X : Cfg, reduced D X ∂haar) -
          (∫ X : Cfg, residue D X ∂haar) := by
            simpa only [Pi.sub_apply] using
              (integral_sub
                ((hred D).integrable_of_hasCompactSupport
                  (HasCompactSupport.of_compactSpace _))
                ((hresidue D).integrable_of_hasCompactSupport
                  (HasCompactSupport.of_compactSpace _)))
      _ = (∫ X : Cfg, reduced D X ∂haar) := by
            rw [hTripleZero, sub_zero]
  have hPairInt (D : Cfg) :
      (∫ X : Cfg, pairs D X ∂haar) =
        (∫ X : Cfg, t2 D e f X ∂haar) +
        (∫ X : Cfg, t2 D e g X ∂haar) +
        (∫ X : Cfg, t2 D f g X ∂haar) := by
    change (∫ X : Cfg,
      (t2 D e f X + t2 D e g X) + t2 D f g X ∂haar) = _
    rw [integral_add ((hi2 D e f).add (hi2 D e g)) (hi2 D f g)]
    rw [integral_add (hi2 D e f) (hi2 D e g)]
  have hSingleInt (D : Cfg) :
      (∫ X : Cfg, singles D X ∂haar) =
        (∫ X : Cfg, t1 D e X ∂haar) +
        (∫ X : Cfg, t1 D f X ∂haar) +
        (∫ X : Cfg, t1 D g X ∂haar) := by
    change (∫ X : Cfg,
      (t1 D e X + t1 D f X) + t1 D g X ∂haar) = _
    rw [integral_add ((hi1 D e).add (hi1 D f)) (hi1 D g)]
    rw [integral_add (hi1 D e) (hi1 D f)]
  have hRedInt (D : Cfg) :
      (∫ X : Cfg, reduced D X ∂haar) =
        ((∫ X : Cfg, t2 D e f X ∂haar) +
          (∫ X : Cfg, t2 D e g X ∂haar) +
          (∫ X : Cfg, t2 D f g X ∂haar)) -
        ((∫ X : Cfg, t1 D e X ∂haar) +
          (∫ X : Cfg, t1 D f X ∂haar) +
          (∫ X : Cfg, t1 D g X ∂haar)) +
        (∫ X : Cfg, w X ∂haar) := by
    change (∫ X : Cfg,
      (pairs D X - singles D X) + w X ∂haar) = _
    rw [integral_add
      ((hpairs D).sub (hsingles D) |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) hiw]
    rw [integral_sub
      ((hpairs D).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((hsingles D).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
    rw [hPairInt, hSingleInt]
  have hFinal :
      (∫ X : Cfg, t3 B X ∂haar) =
        (∫ X : Cfg, t3 I X ∂haar) := by
    calc
      (∫ X : Cfg, t3 B X ∂haar) =
          (∫ X : Cfg, reduced B X ∂haar) := hMoment B
      _ = ((∫ X : Cfg, t2 B e f X ∂haar) +
          (∫ X : Cfg, t2 B e g X ∂haar) +
          (∫ X : Cfg, t2 B f g X ∂haar)) -
        ((∫ X : Cfg, t1 B e X ∂haar) +
          (∫ X : Cfg, t1 B f X ∂haar) +
          (∫ X : Cfg, t1 B g X ∂haar)) +
        (∫ X : Cfg, w X ∂haar) := hRedInt B
      _ = ((∫ X : Cfg, t2 I e f X ∂haar) +
          (∫ X : Cfg, t2 I e g X ∂haar) +
          (∫ X : Cfg, t2 I f g X ∂haar)) -
        ((∫ X : Cfg, t1 I e X ∂haar) +
          (∫ X : Cfg, t1 I f X ∂haar) +
          (∫ X : Cfg, t1 I g X ∂haar)) +
        (∫ X : Cfg, w X ∂haar) := by
          rw [hPair B e f, hPair B e g, hPair B f g,
            hOne B e, hOne B f, hOne B g,
            hOne I e, hOne I f, hOne I g]
      _ = (∫ X : Cfg, reduced I X ∂haar) := (hRedInt I).symm
      _ = (∫ X : Cfg, t3 I X ∂haar) := (hMoment I).symm
  simpa only [t3, w, u, I, Pi.one_apply, mul_one] using hFinal

/-- The COMPLETE original χ_p²-weighted temporal Wilson crossing
CUBE Haar moment is right-boundary INVARIANT. The summation retains
every true ordered temporal-link triple, including diagonal indices. -/
theorem p4Q2PZ12_originalPlaquetteSquare_fullCrossingCubeHaar_invariant
    (p : Plaq) (B : Cfg) :
    (∫ X : Cfg, (χ p X)^2 * (Cross X B)^3 ∂haar) =
    (∫ X : Cfg, (χ p X)^2 *
      (Cross X (fun _ => 1))^3 ∂haar) := by
  let I : Cfg := fun _ => 1
  have hExpand (D : Cfg) :
      (∫ X : Cfg, (χ p X)^2 * (Cross X D)^3 ∂haar) =
      ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ X : Cfg, (χ p X)^2 *
          (E ((X e)⁻¹ * D e) * E ((X f)⁻¹ * D f) *
            E ((X g)⁻¹ * D g)) ∂haar) := by
    simpa only [p4Q2PZ10_originalPlaquettePairThreeCrossingHaar,
      pow_two] using
        (p4Q2PZ10_originalPlaquettePair_fullTripleCrossing_expand H p p D)
  calc
    (∫ X : Cfg, (χ p X)^2 * (Cross X B)^3 ∂haar) =
      ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ X : Cfg, (χ p X)^2 *
          (E ((X e)⁻¹ * B e) * E ((X f)⁻¹ * B f) *
            E ((X g)⁻¹ * B g)) ∂haar) := hExpand B
    _ = ∑ e : Link, ∑ f : Link, ∑ g : Link,
        (∫ X : Cfg, (χ p X)^2 *
          (E ((X e)⁻¹ * I e) * E ((X f)⁻¹ * I f) *
            E ((X g)⁻¹ * I g)) ∂haar) := by
      apply Finset.sum_congr rfl
      intro e _he
      apply Finset.sum_congr rfl
      intro f _hf
      apply Finset.sum_congr rfl
      intro g _hg
      simpa only [I, Pi.one_apply, mul_one] using
        (p4Q2PZ12_originalPlaquetteSquare_threeCrossingLinkHaar_invariant
          H p e f g B)
    _ = (∫ X : Cfg, (χ p X)^2 * (Cross X I)^3 ∂haar) :=
      (hExpand I).symm

/-- The original centered spatial-Wilson-square cubic temporal Haar
moment is independent of the right boundary, ALL finite even periods.
This follows from PZ10 genuine diagonal reduction + PZ12 genuine
diagonal Ward invariance, not an independent-posterior replacement. -/
theorem p4Q2PZ12_originalCenteredSquare_fullCrossingCubeHaar_invariant
    (B : Cfg) :
    (∫ X : Cfg, (h X)^2 * (Cross X B)^3 ∂haar) =
    (∫ X : Cfg, (h X)^2 *
      (Cross X (fun _ => 1))^3 ∂haar) := by
  let I : Cfg := fun _ => 1
  rw [p4Q2PZ10_originalCenteredSpatialSquare_fullCubicHaar_diagonal H B,
    p4Q2PZ10_originalCenteredSpatialSquare_fullCubicHaar_diagonal H I]
  apply congrArg (fun t : ℝ => (1 / 4 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro p _hp
  exact p4Q2PZ12_originalPlaquetteSquare_fullCrossingCubeHaar_invariant
    H p B

end OriginalDiagonalCubicWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ12_originalPlaquetteSquare_threeCrossingLinkHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ12_originalPlaquetteSquare_fullCrossingCubeHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ12_originalCenteredSquare_fullCrossingCubeHaar_invariant
