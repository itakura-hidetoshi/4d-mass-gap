import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRepresentative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceCompleteness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  Fintype.ofFinite _

/-- One-link replacement used by the continuous-vacuum Harnack layer.

This definition is intentionally independent of the older quotient-representative
fiber-distortion module.  The Harnack argument therefore remains pointwise only
on the canonical continuous vacuum representative. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N := by
  classical
  exact Function.update A target g

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A target g target = g := by
  classical
  simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (he : e ≠ target) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A target g e = A e := by
  classical
  simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink, he]

/-- A spatial-slice plaquette touches an intrinsic spatial link when their
canonical four-dimensional embeddings have a physical boundary incidence. -/
def periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Prop :=
  periodicHypercubicPlaquetteTouchesEdge
    (PeriodicHypercubicEvenSideLength H)
    (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)

/-- The finite set of intrinsic spatial plaquettes touching one spatial link. -/
noncomputable def periodicHypercubicEvenSpatialSliceTouchingPlaquettes
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
  classical
  exact Finset.univ.filter fun p =>
    periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target

@[simp] theorem periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target ↔
      periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target := by
  classical
  simp [periodicHypercubicEvenSpatialSliceTouchingPlaquettes]

/-- Even without using the sharper three-dimensional incidence count, every
intrinsic spatial plaquette touching a link embeds into the complete
four-dimensional touching family.  Hence there are at most six such
plaquettes, uniformly in the periodic volume. -/
theorem periodicHypercubicEvenSpatialSliceTouchingPlaquettes_card_le_six
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target).card ≤ 6 := by
  classical
  let s := periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target
  let emb := periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H
  let fullTarget := periodicHypercubicEvenSpatialSliceLinkEmbedding H target
  let fullTouch := periodicHypercubicTouchingPlaquettes
    (PeriodicHypercubicEvenSideLength H) fullTarget
  have hcardImage : (s.image emb).card = s.card := by
    exact Finset.card_image_of_injective s
      (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_injective H)
  have hsubset : s.image emb ⊆ fullTouch := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    have hpTouch :
        periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target :=
      (periodicHypercubicEvenSpatialSlice_mem_touchingPlaquettes_iff H target p).mp hp
    exact (periodicHypercubic_mem_touchingPlaquettes_iff
      (PeriodicHypercubicEvenSideLength H) fullTarget _).mpr hpTouch
  have hle : (s.image emb).card ≤ fullTouch.card := Finset.card_le_card hsubset
  have hfull : fullTouch.card ≤ 6 := by
    exact periodicHypercubicTouchingPlaquettes_card_le_six
      (PeriodicHypercubicEvenSideLength H) fullTarget
  have hsfull : s.card ≤ fullTouch.card := by
    rw [← hcardImage]
    exact hle
  have hsix : s.card ≤ 6 := le_trans hsfull hfull
  simpa [s] using hsix

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_zero
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPhysicalBoundaryEdge
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) 0 =
      periodicHypercubicEvenSpatialSliceLinkEmbedding H (p.1, p.2.1.1) :=
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_one
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPhysicalBoundaryEdge
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) 1 =
      periodicHypercubicEvenSpatialSliceLinkEmbedding H
        (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2) :=
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_two
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPhysicalBoundaryEdge
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) 2 =
      periodicHypercubicEvenSpatialSliceLinkEmbedding H
        (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1) :=
  rfl

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_three
    (H : ℕ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    periodicHypercubicPhysicalBoundaryEdge
        (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p) 3 =
      periodicHypercubicEvenSpatialSliceLinkEmbedding H (p.1, p.2.1.2) :=
  rfl

/-- Replacing a spatial link outside an intrinsic plaquette leaves its
plaquette holonomy unchanged. -/
theorem periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hNotTouches :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p target) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N A target g) p =
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p := by
  classical
  have h0 : (p.1, p.2.1.1) ≠ target := by
    intro h
    apply hNotTouches
    refine ⟨0, ?_⟩
    simpa using congrArg (periodicHypercubicEvenSpatialSliceLinkEmbedding H) h
  have h1 :
      (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2) ≠ target := by
    intro h
    apply hNotTouches
    refine ⟨1, ?_⟩
    simpa using congrArg (periodicHypercubicEvenSpatialSliceLinkEmbedding H) h
  have h2 :
      (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1) ≠ target := by
    intro h
    apply hNotTouches
    refine ⟨2, ?_⟩
    simpa using congrArg (periodicHypercubicEvenSpatialSliceLinkEmbedding H) h
  have h3 : (p.1, p.2.1.2) ≠ target := by
    intro h
    apply hNotTouches
    refine ⟨3, ?_⟩
    simpa using congrArg (periodicHypercubicEvenSpatialSliceLinkEmbedding H) h
  simp [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
    h0, h1, h2, h3]

/-- The intrinsic spatial action is the corresponding finite-universe sum. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  unfold periodicHypercubicEvenSpatialSlicePlaquetteList
  simp

/-- The crossing action is likewise its finite-universe link sum. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  unfold periodicHypercubicEvenSpatialSliceLinkList
  simp

/-- Any two `SU(N)` Wilson plaquette energies differ by at most two. -/
theorem specialUnitaryWilsonPlaquetteEnergy_sub_abs_le_two
    (N : ℕ)
    (hN : 0 < N)
    (U V : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |specialUnitaryWilsonPlaquetteEnergy N U -
      specialUnitaryWilsonPlaquetteEnergy N V| ≤ 2 := by
  have hU0 := specialUnitaryWilsonPlaquetteEnergy_nonneg hN U
  have hU2 := specialUnitaryWilsonPlaquetteEnergy_le_two hN U
  have hV0 := specialUnitaryWilsonPlaquetteEnergy_nonneg hN V
  have hV2 := specialUnitaryWilsonPlaquetteEnergy_le_two hN V
  rw [abs_le]
  constructor <;> linarith

/-- Replacing one spatial link changes the full spatial Wilson action by at
most twelve.  The constant comes from the volume-independent four-dimensional
incidence bound `6` and the exact plaquette-energy width `2`. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuousVacuumReplaceLink_sub_abs_le_twelve
    (H N : ℕ)
    (hN : 0 < N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target g) -
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target h)| ≤ 12 := by
  classical
  let Bg := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target g
  let Bh := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target h
  let Fg := fun p : PeriodicHypercubicEvenSpatialSlicePlaquette H =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy Bg p)
  let Fh := fun p : PeriodicHypercubicEvenSpatialSlicePlaquette H =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy Bh p)
  let s := periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum,
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum,
    ← Finset.sum_sub_distrib]
  change |∑ p, (Fg p - Fh p)| ≤ 12
  calc
    |∑ p, (Fg p - Fh p)| ≤ ∑ p, |Fg p - Fh p| :=
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
          H N B target g p hNotTouches
      have hhEq :=
        periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_continuousVacuumReplaceLink_eq_of_not_touches
          H N B target h p hNotTouches
      change |Fg p - Fh p| = 0
      simp [Fg, Fh, Bg, Bh, hgEq, hhEq]
    _ ≤ ∑ _p ∈ s, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact specialUnitaryWilsonPlaquetteEnergy_sub_abs_le_two N hN _ _
    _ = (s.card : ℝ) * 2 := by simp
    _ ≤ (6 : ℝ) * 2 := by
      gcongr
      exact_mod_cast
        periodicHypercubicEvenSpatialSliceTouchingPlaquettes_card_le_six H target
    _ = 12 := by norm_num

/-- Replacing one boundary link changes the temporal crossing action by at most
two, since exactly one summand can change. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuousVacuumReplaceLink_sub_abs_le_two
    (H N : ℕ)
    (hN : 0 < N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target g) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target h)| ≤ 2 := by
  classical
  let Bg := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target g
  let Bh := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target h
  let Fg := fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
    specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * Bg e)
  let Fh := fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
    specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * Bh e)
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum,
    ← Finset.sum_sub_distrib]
  change |∑ e, (Fg e - Fh e)| ≤ 2
  have hsum :
      (∑ e, (Fg e - Fh e)) = Fg target - Fh target := by
    rw [Finset.sum_eq_single target]
    · intro e _he hne
      have hgEq :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
          H N B target e g hne
      have hhEq :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
          H N B target e h hne
      simp [Fg, Fh, Bg, Bh, hgEq, hhEq]
    · simp
  rw [hsum]
  exact specialUnitaryWilsonPlaquetteEnergy_sub_abs_le_two N hN _ _

/-- The complete symmetric one-slab action has a volume-independent one-link
oscillation bound of eight on the second boundary. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_continuousVacuumReplaceLink_sub_abs_le_eight
    (H N : ℕ)
    (hN : 0 < N)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target g) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target h)| ≤ 8 := by
  let Bg := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target g
  let Bh := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target h
  have hcross :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuousVacuumReplaceLink_sub_abs_le_two
      H N hN A B target g h
  have hspatial :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuousVacuumReplaceLink_sub_abs_le_twelve
      H N hN B target g h
  have hEq :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A Bg -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A Bh =
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bg -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bh) +
        (1 / 2 : ℝ) *
          (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bg -
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bh) := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    ring
  rw [hEq]
  calc
    |(periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bg -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bh) +
        (1 / 2 : ℝ) *
          (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bg -
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bh)| ≤
        |periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bg -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bh| +
        |(1 / 2 : ℝ) *
          (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bg -
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bh)| :=
      abs_add_le _ _
    _ = |periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bg -
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A Bh| +
        (1 / 2 : ℝ) *
          |periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bg -
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N Bh| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 + (1 / 2 : ℝ) * 12 := by
      gcongr
    _ = 8 := by norm_num

/-- Volume-independent local kernel comparison.  Changing one link of the
second spatial boundary costs at most the explicit factor `exp (8 * beta)`.
No compactness minimum and no lattice-volume cardinality enters this bound. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target g) ≤
      Real.exp (8 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N B target h) := by
  let Bg := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target g
  let Bh := periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
    H N B target h
  let Sg := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A Bg
  let Sh := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A Bh
  have hosc :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_continuousVacuumReplaceLink_sub_abs_le_eight
      H N hN A B target g h
  have hdiff : Sh - Sg ≤ 8 := by
    have hlower : -8 ≤ Sg - Sh := (abs_le.mp hosc).1
    linarith
  have hmul : beta * (Sh - Sg) ≤ beta * 8 :=
    mul_le_mul_of_nonneg_left hdiff hbeta
  have hexp : -beta * Sg ≤ 8 * beta + (-beta * Sh) := by
    nlinarith [hmul]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  calc
    Real.exp (-beta * Sg) ≤ Real.exp (8 * beta + (-beta * Sh)) :=
      Real.exp_le_exp.mpr hexp
    _ = Real.exp (8 * beta) * Real.exp (-beta * Sh) := by
      rw [Real.exp_add]

/-- The reverse comparison has the same volume-independent factor. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_reverse_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
          H N B target h) ≤
      Real.exp (8 * beta) *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
            H N B target g) := by
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
      H N hN beta hbeta A B target h g

end

end MathlibAnalytic
end MGAP4D