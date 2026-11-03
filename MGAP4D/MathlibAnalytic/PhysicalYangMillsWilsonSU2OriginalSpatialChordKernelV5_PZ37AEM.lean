import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOneLinkChordKernelModulusV5_PZ37AEM
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyInversion
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceCyclic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEM spatial completion — unconditional original SU(2) kernel bound

The calibrated d_J is the distance in the SAME normalized real-eight
SU(2) feature. Its squared form is twice the ORIGINAL Wilson energy,
so conjugation invariance and inversion invariance prove exact
left/right multiplication and inversion isometries.

A genuine four-edge spatial plaquette holonomy therefore has a chord
variation ≤ 4 d_J(g,h) after ONE original link is changed (the bound is
valid even when a geometric edge occurs more than once in a word).
Only spatial plaquettes touching the changed link may contribute, and
the EXISTING physical incidence certificate bounds their number by 6.

Thus the ORIGINAL spatial Wilson action changes by at most 24 d_J,
and the ORIGINAL one-slab Wilson action by at most 13 d_J.
Together with the previous AEM exponential estimate:

  |K_H(A,B[e↦g])-K_H(A,B[e↦h])| ≤ 13*beta_0*d_J(g,h).

The last inequality is unconditional for every finite H and for the
unchanged original physical Wilson kernel. This bound is uniform in
H but does not by itself give a Perron, rho or q Lipschitz modulus or
the infinite-volume mass gap. No new gauge law or kernel is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

/-- Unconditional Wilson plaquette energy chordal Lipschitz continuity. -/
theorem p4Q2PZ37AEM_originalWilsonEnergy_chordLipschitz
    (g h : G) : |E g - E h| ≤ dJ g h := by
  simpa using
    (p4Q2PZ37AEM_originalRelativeWilsonEnergy_chordLipschitz
      (1 : G) g h)

/-- The genuine normalized SU(2) chord is invariant under left
translation, by the exact calibrated Wilson energy identity. -/
theorem p4Q2PZ37AEM_originalChord_leftMul (a g h : G) :
    dJ (a * g) (a * h) = dJ g h := by
  have hGroup : (a * g)⁻¹ * (a * h) = g⁻¹ * h := by group
  have hSq : (dJ (a * g) (a * h)) ^ 2 = (dJ g h) ^ 2 := by
    calc
      (dJ (a * g) (a * h)) ^ 2 =
          2 * E ((a * g)⁻¹ * (a * h)) :=
        p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy _ _
      _ = 2 * E (g⁻¹ * h) := by rw [hGroup]
      _ = (dJ g h) ^ 2 :=
        (p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy g h).symm
  have hx := p4Q2PZ37ADK_trueChordalDistance_nonneg (a * g) (a * h)
  have hy := p4Q2PZ37ADK_trueChordalDistance_nonneg g h
  nlinarith only [hSq, hx, hy]

/-- The genuine chord is also invariant under right translation,
by conjugation invariance of the original Wilson trace. -/
theorem p4Q2PZ37AEM_originalChord_rightMul (a g h : G) :
    dJ (g * a) (h * a) = dJ g h := by
  have hGroup : (g * a)⁻¹ * (h * a) =
      a⁻¹ * (g⁻¹ * h) * a := by group
  have hConj : E (a⁻¹ * (g⁻¹ * h) * a) = E (g⁻¹ * h) := by
    simpa only [inv_inv] using
      (specialUnitaryWilsonPlaquetteEnergy_conjInvariant (a⁻¹) (g⁻¹ * h))
  have hSq : (dJ (g * a) (h * a)) ^ 2 = (dJ g h) ^ 2 := by
    calc
      (dJ (g * a) (h * a)) ^ 2 =
          2 * E ((g * a)⁻¹ * (h * a)) :=
        p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy _ _
      _ = 2 * E (a⁻¹ * (g⁻¹ * h) * a) := by rw [hGroup]
      _ = 2 * E (g⁻¹ * h) := by rw [hConj]
      _ = (dJ g h) ^ 2 :=
        (p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy g h).symm
  have hx := p4Q2PZ37ADK_trueChordalDistance_nonneg (g * a) (h * a)
  have hy := p4Q2PZ37ADK_trueChordalDistance_nonneg g h
  nlinarith only [hSq, hx, hy]

/-- Inversion is an isometry for the same physical SU(2) chord. -/
theorem p4Q2PZ37AEM_originalChord_inv (g h : G) :
    dJ g⁻¹ h⁻¹ = dJ g h := by
  have hCycle : E (g * h⁻¹) = E (h⁻¹ * g) := by
    simp only [specialUnitaryWilsonPlaquetteEnergy_eq]
    rw [normalizedSpecialUnitaryRealTrace_mul_cycle g h⁻¹]
  have hInv : E (h⁻¹ * g) = E (g⁻¹ * h) := by
    calc
      E (h⁻¹ * g) = E ((g⁻¹ * h)⁻¹) := by
        congr 1
        group
      _ = E (g⁻¹ * h) :=
        specialUnitaryWilsonPlaquetteEnergy_inv (g⁻¹ * h)
  have hSq : (dJ g⁻¹ h⁻¹) ^ 2 = (dJ g h) ^ 2 := by
    calc
      (dJ g⁻¹ h⁻¹) ^ 2 =
          2 * E ((g⁻¹)⁻¹ * h⁻¹) :=
        p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy _ _
      _ = 2 * E (g * h⁻¹) := by rw [inv_inv]
      _ = 2 * E (h⁻¹ * g) := by rw [hCycle]
      _ = 2 * E (g⁻¹ * h) := by rw [hInv]
      _ = (dJ g h) ^ 2 :=
        (p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy g h).symm
  have hx := p4Q2PZ37ADK_trueChordalDistance_nonneg g⁻¹ h⁻¹
  have hy := p4Q2PZ37ADK_trueChordalDistance_nonneg g h
  nlinarith only [hSq, hx, hy]

/-- Finite multiplicative triangle estimate for genuine SU(2) chords. -/
theorem p4Q2PZ37AEM_originalChord_mul_le
    (a b c d : G) :
    dJ (a * b) (c * d) ≤ dJ a c + dJ b d := by
  calc
    dJ (a * b) (c * d) ≤
        dJ (a * b) (c * b) + dJ (c * b) (c * d) :=
      p4Q2PZ37ADK_trueChordalDistance_triangle _ _ _
    _ = dJ a c + dJ b d := by
      rw [p4Q2PZ37AEM_originalChord_rightMul b a c,
        p4Q2PZ37AEM_originalChord_leftMul c b d]

/-- Four-edge Wilson holonomy is 1-Lipschitz per edge, including
the two inverse-oriented edges. -/
theorem p4Q2PZ37AEM_originalFourEdgeWord_chordLe
    (a b c d a' b' c' d' : G) :
    dJ (a * b * c⁻¹ * d⁻¹) (a' * b' * c'⁻¹ * d'⁻¹) ≤
      dJ a a' + dJ b b' + dJ c c' + dJ d d' := by
  have h0 : dJ (a * b) (a' * b') ≤ dJ a a' + dJ b b' :=
    p4Q2PZ37AEM_originalChord_mul_le a b a' b'
  have h1 : dJ (a * b * c⁻¹) (a' * b' * c'⁻¹) ≤
      dJ (a * b) (a' * b') + dJ c⁻¹ c'⁻¹ :=
    p4Q2PZ37AEM_originalChord_mul_le (a * b) c⁻¹ (a' * b') c'⁻¹
  have h2 : dJ (a * b * c⁻¹ * d⁻¹) (a' * b' * c'⁻¹ * d'⁻¹) ≤
      dJ (a * b * c⁻¹) (a' * b' * c'⁻¹) + dJ d⁻¹ d'⁻¹ :=
    p4Q2PZ37AEM_originalChord_mul_le
      (a * b * c⁻¹) d⁻¹ (a' * b' * c'⁻¹) d'⁻¹
  rw [p4Q2PZ37AEM_originalChord_inv] at h1 h2
  nlinarith only [h0, h1, h2]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "Hol" =>
  periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "Spatial" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Kernel" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0

local instance p4Q2PZ37AEM_spatialLinks : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEM_spatialPlaquettes : Fintype Plaq := Fintype.ofFinite _

/-- Replacing exactly one true coordinate changes ANY selected
spatial-link chord by at most the chord of the inserted holonomies. -/
theorem p4Q2PZ37AEM_originalReplaceLink_coordinate_chordLe
    (B : Cfg) (target j : Link) (g h : G) :
    dJ ((Replace B target g) j) ((Replace B target h) j) ≤ dJ g h := by
  classical
  by_cases heq : j = target
  · subst j
    simpa [Replace,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (le_refl (dJ g h))
  · rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
          H 2 B target j g heq,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
          H 2 B target j h heq,
        p4Q2PZ37ADK_trueChordalDistance_self]
    exact p4Q2PZ37ADK_trueChordalDistance_nonneg g h

/-- Every ORIGINAL spatial plaquette holonomy has a uniform
four-edge chordal variation when one actual link is replaced.
No unproved unique-edge-incidence assertion is used. -/
theorem p4Q2PZ37AEM_originalSpatialHolonomy_oneLinkChordLe
    (B : Cfg) (target : Link) (g h : G) (p : Plaq) :
    dJ (Hol (Replace B target g) p) (Hol (Replace B target h) p) ≤
      4 * dJ g h := by
  let Bg := Replace B target g
  let Bh := Replace B target h
  let e0 : Link := (p.1, p.2.1.1)
  let e1 : Link :=
    (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2)
  let e2 : Link :=
    (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1)
  let e3 : Link := (p.1, p.2.1.2)
  have hFour :=
    p4Q2PZ37AEM_originalFourEdgeWord_chordLe
      (Bg e0) (Bg e1) (Bg e2) (Bg e3)
      (Bh e0) (Bh e1) (Bh e2) (Bh e3)
  have h0 :=
    p4Q2PZ37AEM_originalReplaceLink_coordinate_chordLe H B target e0 g h
  have h1 :=
    p4Q2PZ37AEM_originalReplaceLink_coordinate_chordLe H B target e1 g h
  have h2 :=
    p4Q2PZ37AEM_originalReplaceLink_coordinate_chordLe H B target e2 g h
  have h3 :=
    p4Q2PZ37AEM_originalReplaceLink_coordinate_chordLe H B target e3 g h
  have hDef :
      dJ (Hol Bg p) (Hol Bh p) =
        dJ (Bg e0 * Bg e1 * (Bg e2)⁻¹ * (Bg e3)⁻¹)
          (Bh e0 * Bh e1 * (Bh e2)⁻¹ * (Bh e3)⁻¹) := rfl
  rw [hDef]
  nlinarith only [hFour, h0, h1, h2, h3]

/-- The original Wilson energy at each spatial plaquette changes by
at most four times the true single-link chordal displacement. -/
theorem p4Q2PZ37AEM_originalSpatialPlaquetteEnergy_oneLinkChordLe
    (B : Cfg) (target : Link) (g h : G) (p : Plaq) :
    |E (Hol (Replace B target g) p) -
      E (Hol (Replace B target h) p)| ≤ 4 * dJ g h := by
  calc
    |E (Hol (Replace B target g) p) -
      E (Hol (Replace B target h) p)| ≤
        dJ (Hol (Replace B target g) p)
          (Hol (Replace B target h) p) :=
      p4Q2PZ37AEM_originalWilsonEnergy_chordLipschitz _ _
    _ ≤ 4 * dJ g h :=
      p4Q2PZ37AEM_originalSpatialHolonomy_oneLinkChordLe H B target g h p

/-- ORIGINAL finite-incidence physical spatial action bound:
at most six affected plaquettes, each bounded by four chords.
The constant 24 is independent of H, and is deliberately
conservative about repeated edge occurrences. -/
theorem p4Q2PZ37AEM_originalSpatialAction_oneLinkChordLipschitz
    (B : Cfg) (target : Link) (g h : G) :
    |Spatial (Replace B target g) -
      Spatial (Replace B target h)| ≤ 24 * dJ g h := by
  classical
  let Bg := Replace B target g
  let Bh := Replace B target h
  let Fg := fun p : Plaq => E (Hol Bg p)
  let Fh := fun p : Plaq => E (Hol Bh p)
  let s := periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum,
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum,
    ← Finset.sum_sub_distrib]
  change |∑ p : Plaq, (Fg p - Fh p)| ≤ 24 * dJ g h
  calc
    |∑ p : Plaq, (Fg p - Fh p)| ≤
        ∑ p : Plaq, |Fg p - Fh p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ s, |Fg p - Fh p| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro p _hp hps
      have hNotTouches :
          ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target := by
        simpa [s, periodicHypercubicEvenSpatialSliceTouchingPlaquettes] using hps
      have hgEq :=
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H 2 B target g p hNotTouches
      have hhEq :=
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H 2 B target h p hNotTouches
      change |Fg p - Fh p| = 0
      simp [Fg, Fh, Bg, Bh, hgEq, hhEq]
    _ ≤ ∑ _p ∈ s, (4 * dJ g h) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact p4Q2PZ37AEM_originalSpatialPlaquetteEnergy_oneLinkChordLe
        H B target g h p
    _ = (s.card : ℝ) * (4 * dJ g h) := by simp
    _ ≤ 6 * (4 * dJ g h) := by
      have hc : (s.card : ℝ) ≤ 6 := by
        exact_mod_cast
          periodicHypercubicEvenSpatialSliceTouchingPlaquettes_card_le_six H target
      exact mul_le_mul_of_nonneg_right hc (by
        have hd := p4Q2PZ37ADK_trueChordalDistance_nonneg g h
        positivity)
    _ = 24 * dJ g h := by ring

/-- UNCONDITIONAL genuine original one-slab kernel Lipschitz bound
for every finite periodic H. In contrast to AEL's coarse Harnack,
this variation tends to zero linearly with d_J(g,h).
The explicit coefficient 13*beta_0 comes from
one true temporal crossing edge and at most six true spatial
plaquettes with four terms each and the symmetric half action. -/
theorem p4Q2PZ37AEM_originalOneSlabKernel_unconditionalChordLipschitz
    (A B : Cfg) (target : Link) (g h : G) :
    |Kernel A (Replace B target g) -
      Kernel A (Replace B target h)| ≤
      (13 * b0) * dJ g h := by
  have hSpatial :=
    p4Q2PZ37AEM_originalSpatialAction_oneLinkChordLipschitz
      H B target g h
  have hKernel :=
    p4Q2PZ37AEM_originalOneSlabKernel_chordLipschitz_of_spatial
      H A B target g h 24 (by norm_num) hSpatial
  convert hKernel using 1 <;> ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalWilsonEnergy_chordLipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalChord_leftMul
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalChord_rightMul
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalChord_inv
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalChord_mul_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalFourEdgeWord_chordLe
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalReplaceLink_coordinate_chordLe
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalSpatialHolonomy_oneLinkChordLe
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalSpatialPlaquetteEnergy_oneLinkChordLe
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalSpatialAction_oneLinkChordLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalOneSlabKernel_unconditionalChordLipschitz
