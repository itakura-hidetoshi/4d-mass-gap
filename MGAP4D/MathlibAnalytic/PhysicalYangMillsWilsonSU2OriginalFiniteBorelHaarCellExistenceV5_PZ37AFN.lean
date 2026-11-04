import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalReceiverSectionChordalSlopeV5_PZ37AFM
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHaarFiniteNetCertificateV5_PZ37ADP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFN — original SU(2) finite Borel Haar cells and rational existence

AFM removed every EXTERNAL receiver and four-mode Lipschitz/envelope
premise from the original certified Haar cell and sample chain.
AFN makes the remaining ORIGINAL SU(2) geometry available at any
positive chordal radius, by the already-proved ADP compact finite net.

A finite ordered true SU(2) ball cover is converted to disjoint
measurable cells by assigning each group element to its FIRST
qualifying center. The cells cover the entire original group
without overlap, and each lies in its original d_J ball.

The finite masses refer to the unchanged normalized compact Haar.
Density of the rationals supplies a *noncomputable existence proof*
of arbitrarily accurate rational enclosures of these real masses
and true Wilson/Perron FF point samples, including their squares
and products with the genuine quaternion characters.
This is NOT a finite numerical algorithm, not an explicit grid
cardinality bound, and NOT a verified numerical witness/crossing.
In particular the existence of rational approximants by classical
choice does not certify any particular machine-generated table.

The physical receiver, true original Haar law, source, Perron,
full-link metric, FC obstruction, and pinned Lean/mathlib are unchanged.
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
local notation "BallJ" => p4Q2PZ37ADK_trueChordalBall
local notation "mu" => normalizedCompactHaar G

local instance p4Q2PZ37AFN_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFN_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFN_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFN_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFN_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFN_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Rational density gives a finite absolute-error enclosure
for ANY real value and positive tolerance. It is an existence
theorem, not an effective bound on an evaluated rational. -/
theorem p4Q2PZ37AFN_exists_rational_absoluteEnclosure
    (x eps : ℝ) (heps : 0 < eps) :
    ∃ q : ℚ, |x - (q : ℝ)| ≤ eps := by
  have hRange : x - eps < x + eps := by linarith only [heps]
  obtain ⟨q, hLo, hHi⟩ := exists_rat_btwn hRange
  refine ⟨q, abs_le.mpr ?_⟩
  constructor <;> linarith only [hLo, hHi]

noncomputable def p4Q2PZ37AFN_rationalEnclosure
    (x eps : ℝ) (heps : 0 < eps) : ℚ :=
  Classical.choose
    (p4Q2PZ37AFN_exists_rational_absoluteEnclosure x eps heps)

theorem p4Q2PZ37AFN_rationalEnclosure_error
    (x eps : ℝ) (heps : 0 < eps) :
    |x - (p4Q2PZ37AFN_rationalEnclosure x eps heps : ℝ)| ≤ eps :=
  Classical.choose_spec
    (p4Q2PZ37AFN_exists_rational_absoluteEnclosure x eps heps)

/-- Actual first-center tie-breaking of FINITELY many genuine
SU(2) d_J-open balls; no proxy geometry or discrete Haar. -/
def p4Q2PZ37AFN_originalFirstCenterCell
    (n : ℕ) (centers : Fin n → G) (r : ℝ) (i : Fin n) : Set G :=
  (BallJ (centers i) r) \
    ⋃ j : Fin n, if j < i then BallJ (centers j) r else ∅

theorem p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
    (n : ℕ) (centers : Fin n → G) (r : ℝ) (i : Fin n) (g : G) :
    g ∈ p4Q2PZ37AFN_originalFirstCenterCell n centers r i ↔
      g ∈ BallJ (centers i) r ∧
        ∀ j : Fin n, j < i → g ∉ BallJ (centers j) r := by
  unfold p4Q2PZ37AFN_originalFirstCenterCell
  constructor
  · rintro ⟨hi, hNone⟩
    refine ⟨hi, ?_⟩
    intro j hji hj
    apply hNone
    exact Set.mem_iUnion.mpr ⟨j, by simpa only [if_pos hji] using hj⟩
  · rintro ⟨hi, hNone⟩
    refine ⟨hi, ?_⟩
    intro hUnion
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hUnion
    by_cases hji : j < i
    · exact hNone j hji (by simpa only [if_pos hji] using hj)
    · simpa only [if_neg hji] using hj

/-- True SU(2) Borel measurability of each tie-broken cell:
open Wilson-feature balls minus a finite (hence Borel) union. -/
theorem p4Q2PZ37AFN_originalFirstCenterCell_measurable
    (n : ℕ) (centers : Fin n → G) (r : ℝ) (i : Fin n) :
    MeasurableSet (p4Q2PZ37AFN_originalFirstCenterCell n centers r i) := by
  unfold p4Q2PZ37AFN_originalFirstCenterCell
  apply (p4Q2PZ37ADK_trueChordalBall_isOpen (centers i) r).measurableSet.diff
  apply MeasurableSet.iUnion
  intro j
  by_cases hji : j < i
  · simpa only [if_pos hji] using
      (p4Q2PZ37ADK_trueChordalBall_isOpen (centers j) r).measurableSet
  · simpa only [if_neg hji] using (MeasurableSet.empty : MeasurableSet (∅ : Set G))

/-- Any finite ball cover of original SU(2) becomes an exact
non-overlapping Borel partition, with the original center radius. -/
theorem p4Q2PZ37AFN_originalFirstCenterCell_partition
    (n : ℕ) (centers : Fin n → G) (r : ℝ)
    (hCover : ∀ g : G, ∃ i : Fin n, g ∈ BallJ (centers i) r) :
    ∀ g : G, ∃ i : Fin n,
      g ∈ p4Q2PZ37AFN_originalFirstCenterCell n centers r i ∧
      ∀ j : Fin n,
        g ∈ p4Q2PZ37AFN_originalFirstCenterCell n centers r j → j = i := by
  intro g
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => g ∈ BallJ (centers i) r)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hCover g
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hMin⟩ := Finset.exists_min_image s (fun i : Fin n => i) hs
  have hBall : g ∈ BallJ (centers i) r := (Finset.mem_filter.mp hi).2
  have hPrior : ∀ j : Fin n, j < i → g ∉ BallJ (centers j) r := by
    intro j hji hj
    have hjMem : j ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    have hle : i ≤ j := hMin j hjMem
    exact (not_le_of_gt hji) hle
  have hChosen :
      g ∈ p4Q2PZ37AFN_originalFirstCenterCell n centers r i :=
    (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff n centers r i g).2
      ⟨hBall, hPrior⟩
  refine ⟨i, hChosen, ?_⟩
  intro j hj
  obtain ⟨hjBall, hjPrior⟩ :=
    (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
      n centers r j g).1 hj
  rcases lt_trichotomy i j with hij | heq | hji
  · exact False.elim (hjPrior i hij hBall)
  · exact heq.symm
  · exact False.elim (hPrior j hji hjBall)

/-- An ordered genuine ball cover creates an AFJ typed Haar
partition with arbitrarily small TRUE-mass rational interval
errors. The rational weights come from dense rational choice,
not from a numerical measurement. -/
noncomputable def p4Q2PZ37AFN_originalHaarCells_of_finiteCover
    (n : ℕ) (centers : Fin n → G) (r eps : ℝ)
    (hCover : ∀ g : G, ∃ i : Fin n, g ∈ BallJ (centers i) r)
    (heps : 0 < eps) :
    GroundStatePosteriorJoint.p4Q2PZ37AFJ_originalHaarCells where
  n := n
  cell := p4Q2PZ37AFN_originalFirstCenterCell n centers r
  hMeas := p4Q2PZ37AFN_originalFirstCenterCell_measurable n centers r
  hPartition :=
    p4Q2PZ37AFN_originalFirstCenterCell_partition n centers r hCover
  weight := fun i =>
    p4Q2PZ37AFN_rationalEnclosure
      (Measure.real mu (p4Q2PZ37AFN_originalFirstCenterCell n centers r i))
      eps heps
  weightError := fun _ => eps
  hWeightError_nonneg := by intro i; exact heps.le
  hWeightAccuracy := by
    intro i
    exact p4Q2PZ37AFN_rationalEnclosure_error
      (Measure.real mu (p4Q2PZ37AFN_originalFirstCenterCell n centers r i))
      eps heps

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter

local instance p4Q2PZ37AFN_links : Fintype Link := Fintype.ofFinite _

/-- Every genuine finite ball cover yields an actual AFM
numeric-only original receiver certificate, with rational point
values chosen noncomputably at ANY tolerance. The same literal
FF receiver is sampled for mean, second moment, and four modes. -/
noncomputable def p4Q2PZ37AFN_originalSamples_of_finiteCover
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (n : ℕ) (centers : Fin n → G) (r epsWeight epsSample : ℝ)
    (hr : 0 < r) (hw : 0 < epsWeight) (hs : 0 < epsSample)
    (hCover : ∀ g : G, ∃ i : Fin n, g ∈ BallJ (centers i) r) :
    p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c where
  partition :=
    p4Q2PZ37AFN_originalHaarCells_of_finiteCover
      n centers r epsWeight hCover hw
  center := centers
  radius := r
  hRadius := hr.le
  hCellRadius := by
    intro i g hgi
    have hBall : g ∈ BallJ (centers i) r :=
      (p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
        n centers r i g).1 hgi |>.1
    calc
      dJ g (centers i) = dJ (centers i) g :=
        p4Q2PZ37ADK_trueChordalDistance_symm g (centers i)
      _ ≤ r := le_of_lt hBall
  hThetaLo := hlo
  meanSample := fun a i =>
    p4Q2PZ37AFN_rationalEnclosure (F e a (centers i)) epsSample hs
  meanSampleError := fun _ => epsSample
  hMeanSampleError_nonneg := by intro a ha; exact hs.le
  hMeanSample := by
    intro a ha i
    exact p4Q2PZ37AFN_rationalEnclosure_error
      (F e a (centers i)) epsSample hs
  secondSample := fun a i =>
    p4Q2PZ37AFN_rationalEnclosure ((F e a (centers i)) ^ 2) epsSample hs
  secondSampleError := fun _ => epsSample
  hSecondSampleError_nonneg := by intro a ha; exact hs.le
  hSecondSample := by
    intro a ha i
    exact p4Q2PZ37AFN_rationalEnclosure_error
      ((F e a (centers i)) ^ 2) epsSample hs
  coefficientSample := fun a j i =>
    p4Q2PZ37AFN_rationalEnclosure
      (F e a (centers i) * phi j (centers i)) epsSample hs
  coefficientSampleError := fun _ _ => epsSample
  hCoefficientSampleError_nonneg := by intro a ha j; exact hs.le
  hCoefficientSample := by
    intro a ha j i
    exact p4Q2PZ37AFN_rationalEnclosure_error
      (F e a (centers i) * phi j (centers i)) epsSample hs

/-- For ANY positive genuine chordal radius, AFN constructs
an AFM original numeric-only certificate from ADP's genuine
compact finite net, with arbitrary rational existence tolerances.
No numerical points/table/strict shell centers are produced. -/
theorem p4Q2PZ37AFN_exists_originalFiniteHaarCellSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (r epsWeight epsSample : ℝ)
    (hr : 0 < r) (hw : 0 < epsWeight) (hs : 0 < epsSample) :
    ∃ d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c,
      d.radius = r := by
  classical
  obtain ⟨s, hNet⟩ := p4Q2PZ37ADP_exists_trueFiniteChordalNet r hr
  let n : ℕ := s.card
  let centers : Fin n → G := fun i => ((Finset.equivFin s).symm i).1
  have hCover : ∀ g : G, ∃ i : Fin n, g ∈ BallJ (centers i) r := by
    intro g
    obtain ⟨a, ha, hag⟩ := hNet g
    refine ⟨Finset.equivFin s ⟨a, ha⟩, ?_⟩
    simpa [n, centers, p4Q2PZ37ADK_trueChordalBall] using hag
  refine ⟨p4Q2PZ37AFN_originalSamples_of_finiteCover
    H e c hlo n centers r epsWeight epsSample hr hw hs hCover, rfl⟩

/-- For each ACTUALLY chosen AFN certificate, the original
AFM->AFL->AFK typed chain is present without external physical
receiver/character envelopes or slopes. It does not assert that
any true two-sign shell center passes the residual thresholds. -/
theorem p4Q2PZ37AFN_exists_trueCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo) (r epsWeight epsSample : ℝ)
    (hr : 0 < r) (hw : 0 < epsWeight) (hs : 0 < epsSample) :
    ∃ d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c,
      d.radius = r ∧
      Nonempty (p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c) := by
  obtain ⟨d, hRadius⟩ :=
    p4Q2PZ37AFN_exists_originalFiniteHaarCellSamples
      H e c hlo r epsWeight epsSample hr hw hs
  exact ⟨d, hRadius, ⟨p4Q2PZ37AFM_toOriginalCoefficientVarianceCertificate
    H e c d⟩⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFN_exists_rational_absoluteEnclosure
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFN_rationalEnclosure_error
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFN_originalFirstCenterCell_mem_iff
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFN_originalFirstCenterCell_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFN_originalFirstCenterCell_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFN_exists_originalFiniteHaarCellSamples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFN_exists_trueCoefficientVarianceCertificate
