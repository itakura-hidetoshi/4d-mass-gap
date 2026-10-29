import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllLinkTemporalHaarRestrictionV5_PZ37ABP
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABQ — true four-edge spatial/Perron weight comparison

The original symmetric one-slab kernel contains the spatial Wilson
half-weight on each boundary. Combine the existing actual one-link
spatial-action variation (at most 12) and the pointwise continuous
Perron vacuum Harnack bound (exp (8*b)) to bound the TRUE left
spatial-half-weight times its Perron representative by exp (14*b)
under one actual-link update. A finite-coordinate telescope then gives
exp (56*b) across MY's four genuine plaquette edges, independently
of the number of remote links (including H=0).

The two configurations must agree on the full actual remote-link
complement. No posterior independence, volume-uniform GI floor,
signed receiver overlap or physical transfer-norm normalization
is inferred. All original kernel/Perron/physical-source definitions
and earlier results are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

/-!
The decidable equality is an explicit parameter of both generic
Harnack telescope lemmas. This forces the function updates in their
statements, proofs and Wilson specialization to use the SAME instance.
Previously a hidden Classical.propDecidable competed with the native
finite-link instDecidableEqProd, causing whnf loops and then a real
Function.update instance mismatch after locally sealing large definitions.
-/
/-- A one-coordinate comparison telescopes exactly across a finite support.
The support is the set of coordinates where the configurations may differ. -/
theorem p4Q2PZ37ABQ_finiteCoordinateHarnack
    {ι : Type*} {α : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → α) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ (B : ι → α) (i : ι) (g : α),
      F (Function.update B i g) ≤ c * F B)
    (s : Finset ι) :
    ∀ (A B : ι → α), (∀ i, i ∉ s → A i = B i) →
      F A ≤ c ^ s.card * F B := by
  induction s using Finset.induction_on with
  | empty =>
      intro A B h
      have hAB : A = B := by
        funext i
        exact h i (by simp)
      subst B
      simp
  | @insert i s hi ih =>
      intro A B h
      let B' : ι → α := Function.update B i (A i)
      have hrem : ∀ j, j ∉ s → A j = B' j := by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp [B']
        · have hnot : j ∉ insert i s := by simp [hji, hj]
          have hjEq := h j hnot
          simpa [B', hji] using hjEq
      calc
        F A ≤ c ^ s.card * F B' := ih A B' hrem
        _ ≤ c ^ s.card * (c * F B) :=
          mul_le_mul_of_nonneg_left (hstep B i (A i)) (pow_nonneg hc _)
        _ = c ^ (insert i s).card * F B := by
          rw [Finset.card_insert_of_notMem hi, pow_succ]
          ring


/-- A four-coordinate version of the finite-coordinate Harnack telescope.
The support and cardinality calculation are performed in a small generic
type, before specializing to the actual Wilson-link geometry. -/
theorem p4Q2PZ37ABQ_finiteFourCoordinateHarnack
    {ι : Type*} {α : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → α) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ (B : ι → α) (i : ι) (g : α),
      F (Function.update B i g) ≤ c * F B)
    (e : Fin 4 ↪ ι) (A B : ι → α)
    (hremote : ∀ i : ι, i ∉ Set.range e → A i = B i) :
    F A ≤ c ^ 4 * F B := by
  let s : Finset ι := Finset.univ.image e
  have hcard : s.card = 4 := by
    dsimp [s]
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin 4)) e.injective]
    simp
  have hagree : ∀ i : ι, i ∉ s → A i = B i := by
    intro i hi
    apply hremote i
    intro hr
    rcases hr with ⟨j, hj⟩
    apply hi
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have h := p4Q2PZ37ABQ_finiteCoordinateHarnack F c hc hstep s A B hagree
  simpa only [hcard] using h

/-- The fixed four-link Harnack factor is independent of the number of
unselected links. -/
private theorem p4Q2PZ37ABQ_exp_four (b : ℝ) :
    (Real.exp (14 * b)) ^ 4 = Real.exp (56 * b) := by
  rw [show (56 : ℝ) * b =
    (14 * b) + (14 * b) + (14 * b) + (14 * b) by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_add]
  ring

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ABQ_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABQ_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABQ_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABQ_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABQ_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local instance p4Q2PZ37ABQ_linkFintype : Fintype Link := Fintype.ofFinite _

/-- The genuine spatial Wilson half-weight multiplied by the actual
strictly positive continuous Perron representative on the same slice. -/
noncomputable def p4Q2PZ37ABQ_originalSpatialPerronWeight
    (b : ℝ) (hb : 0 ≤ b) (A : Cfg) : ℝ :=
  Real.exp (-(b / 2 *
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A)) *
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) b hb A

/-- The original spatial/Perron boundary factor is pointwise positive. -/
theorem p4Q2PZ37ABQ_originalSpatialPerronWeight_pos
    (b : ℝ) (hb : 0 ≤ b) (A : Cfg) :
    0 < p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb A := by
  unfold p4Q2PZ37ABQ_originalSpatialPerronWeight
  exact mul_pos (Real.exp_pos _)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) b hb A)

/-- A single genuine spatial link modifies the original spatial half-weight
by at most exp(6*b) and the original Perron representative by exp(8*b).
Thus their product has the independent-of-volume factor exp(14*b). -/
theorem p4Q2PZ37ABQ_originalSpatialPerronWeight_oneLink_le
    (b : ℝ) (hb : 0 ≤ b) (A : Cfg) (target : Link) (g h : G) :
    p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb
        (Function.update A target g) ≤
      Real.exp (14 * b) *
        p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb
          (Function.update A target h) := by
  classical
  let Bg : Cfg := Function.update A target g
  let Bh : Cfg := Function.update A target h
  let omega : Cfg → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 (by norm_num) b hb
  let a : ℝ := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 Bg
  let d : ℝ := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 Bh
  let theta : ℝ := b / 2
  have hs : |a - d| ≤ 12 := by
    simpa [a, d, Bg, Bh,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuousVacuumReplaceLink_sub_abs_le_twelve
        H 2 (by norm_num) A target g h)
  have hreverse : d - a ≤ 12 := by
    have h := (abs_le.mp hs).1
    linarith
  have htheta : 0 ≤ theta := div_nonneg hb (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hreverse htheta
  have hlog : -(theta * a) ≤ 6 * b + -(theta * d) := by
    dsimp [theta] at *
    nlinarith [hscaled]
  have hEnergy :
      Real.exp (-(theta * a)) ≤
        Real.exp (6 * b) * Real.exp (-(theta * d)) := by
    calc
      _ ≤ Real.exp (6 * b + -(theta * d)) := Real.exp_le_exp.mpr hlog
      _ = _ := by rw [Real.exp_add]
  have hOmega : omega Bg ≤ Real.exp (8 * b) * omega Bh := by
    simpa [omega, Bg, Bh] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_update_right_le_exp_eight_mul_update_right
        H 2 (by norm_num) b hb A target g h)
  have hOg : 0 ≤ omega Bg :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (by norm_num) b hb Bg).le
  have hCore :
      Real.exp (-(theta * a)) * omega Bg ≤
        Real.exp (14 * b) * (Real.exp (-(theta * d)) * omega Bh) := by
    calc
      _ ≤ (Real.exp (6 * b) * Real.exp (-(theta * d))) * omega Bg :=
        mul_le_mul_of_nonneg_right hEnergy hOg
      _ ≤ (Real.exp (6 * b) * Real.exp (-(theta * d))) *
          (Real.exp (8 * b) * omega Bh) :=
        mul_le_mul_of_nonneg_left hOmega
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = (Real.exp (6 * b) * Real.exp (8 * b)) *
          (Real.exp (-(theta * d)) * omega Bh) := by ring
      _ = _ := by
        have hexp : Real.exp (6 * b) * Real.exp (8 * b) = Real.exp (14 * b) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
  change
    Real.exp (-(theta * a)) * omega Bg ≤
      Real.exp (14 * b) * (Real.exp (-(theta * d)) * omega Bh)
  exact hCore

/-!
The four-edge proof only needs the already verified *named* local weight
and geometric embedding. Prevent the elaborator from unfolding their very
large definitions in speculative whnf/isDefEq checks. This is a locally
scoped transparency choice; the physical definitions and all earlier
one-link proofs remain unchanged.
-/
attribute [local irreducible]
  p4Q2PZ37ABQ_originalSpatialPerronWeight
  p4Q2MY_originalPlaquetteFourEdgeEmbedding

/-- Four true plaquette links, with the remote configuration unchanged,
have a uniform original spatial-Perron weight comparison. The four-link
support is MY's genuinely injective embedding (also at H=0). -/
theorem p4Q2PZ37ABQ_originalSpatialPerronWeight_fourEdge_le
    (b : ℝ) (hb : 0 ≤ b) (p : Plaq) (A B : Cfg)
    (hremote : ∀ e : Link,
      e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p) →
        A e = B e) :
    p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb A ≤
      Real.exp (56 * b) *
        p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb B := by
  let W : Cfg → ℝ := p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb
  have hstep : ∀ (C : Cfg) (target : Link) (g : G),
      W (Function.update C target g) ≤ Real.exp (14 * b) * W C := by
    intro C target g
    have hId : Function.update C target (C target) = C := by
      funext i
      by_cases hi : i = target
      · subst i
        simp
      · simp [hi]
    have h := p4Q2PZ37ABQ_originalSpatialPerronWeight_oneLink_le
      H b hb C target g (C target)
    rw [hId] at h
    exact h
  have hFour : W A ≤ (Real.exp (14 * b)) ^ 4 * W B :=
    p4Q2PZ37ABQ_finiteFourCoordinateHarnack
      (ι := Link) (α := G)
      W (Real.exp (14 * b)) (Real.exp_nonneg _) hstep
      (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p) A B hremote
  have hCoef : (Real.exp (14 * b)) ^ 4 * W B =
      Real.exp (56 * b) * W B :=
    congrArg (fun c : ℝ => c * W B) (p4Q2PZ37ABQ_exp_four b)
  exact hFour.trans_eq hCoef

/-- The comparison is symmetric because both configurations have the same
actual remote links; no global volume factor is introduced. -/
theorem p4Q2PZ37ABQ_originalSpatialPerronWeight_fourEdge_pairwise
    (b : ℝ) (hb : 0 ≤ b) (p : Plaq) (A B : Cfg)
    (hremote : ∀ e : Link,
      e ∉ Set.range (p4Q2MY_originalPlaquetteFourEdgeEmbedding H p) →
        A e = B e) :
    p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb A ≤
        Real.exp (56 * b) *
          p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb B ∧
      p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb B ≤
        Real.exp (56 * b) *
          p4Q2PZ37ABQ_originalSpatialPerronWeight H b hb A := by
  constructor
  · exact p4Q2PZ37ABQ_originalSpatialPerronWeight_fourEdge_le
      H b hb p A B hremote
  · exact p4Q2PZ37ABQ_originalSpatialPerronWeight_fourEdge_le
      H b hb p B A (fun e he => (hremote e he).symm)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABQ_finiteCoordinateHarnack
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABQ_finiteFourCoordinateHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ_originalSpatialPerronWeight_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ_originalSpatialPerronWeight_oneLink_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ_originalSpatialPerronWeight_fourEdge_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABQ_originalSpatialPerronWeight_fourEdge_pairwise
