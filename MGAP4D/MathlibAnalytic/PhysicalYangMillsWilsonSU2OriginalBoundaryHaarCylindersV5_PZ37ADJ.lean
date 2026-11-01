import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNumericHaarMassObstructionV5_PZ37ADI
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarCapsV5_PZ37ABV
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADJ — original boundary pair-Haar cylinders with explicit SU(2) mass

ADI identified a necessary 1/17 actual Haar-mass threshold for ADH's
specific STRICT sufficient single-ball certificate. ABV independently
proves a genuine Haar SU(2) Wilson-energy cap of mass at least 1/8,
using eight original quaternion group translations, NOT finite-group Haar.

The present appendix transports that existing EXPLICIT cap measure
to the SAME finite-volume original Wilson boundary-pair law
ν_H = (⊗_e μ_SU2) ⊗ (⊗_e μ_SU2), via the genuine first-boundary
link projection. For EVERY original link and EVERY H, a FIXED open
one-coordinate cylinder with E(g)<3/4 has actual pair-Haar mass
>=1/8 > 1/17. The corresponding genuinely translated cylinders
are all open and mass >=1/8; eight cylinders cover the WHOLE
original boundary-pair configuration space.

Every actual ACI nonzero centered-source covariance point therefore
belongs to some large-mass translated open cylinder, and the true
covariance has a smaller OPEN positive-Haar subset of it with
positive amplitude and ADE's exact moment lower bound.

Crucial obstruction: a *large parent cylinder* of mass >=1/8 does
NOT imply that its *smaller covariance-stable region* has mass
>=1/17. No physical Lipschitz coefficient, calibrated metric ball,
pointwise nonzero covariance amplitude, threshold crossing or mass gap
is manufactured. The pair-of-boundary coordinates separately recovers
ABV's 1/64 cap mass in the SAME original outer boundary law.
The model, receiver, physical centered Gauss-law source, Perron
section, both interacting posteriors and pair-Haar law are UNCHANGED.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance p4Q2PZ37ADJ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADJ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADJ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADJ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADJ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADJ_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- An actual SU(2) OPEN Wilson energy cap which contains the
previously proved quantitative 1/8-mass CLOSED genuine Haar cap.
The relaxed 3/4 threshold is explicit, not a new independent law. -/
def p4Q2PZ37ADJ_oneLinkOpenEnergyCap : Set G :=
  {g | E g < (3 / 4 : ℝ)}

theorem p4Q2PZ37ADJ_oneLinkOpenEnergyCap_isOpen :
    IsOpen p4Q2PZ37ADJ_oneLinkOpenEnergyCap := by
  exact isOpen_lt (continuous_specialUnitaryWilsonPlaquetteEnergy 2) continuous_const

theorem p4Q2PZ37ADJ_originalLowCap_subset_openEnergyCap :
    p4Q2PZ37ABV_lowEnergyCap ⊆ p4Q2PZ37ADJ_oneLinkOpenEnergyCap := by
  intro g hg
  change E g ≤ (1 / 2 : ℝ) at hg
  change E g < (3 / 4 : ℝ)
  linarith

/-- Quantitative TRUE normalized SU(2) Haar probability, without
assuming any mass for a made-up or discretized measure. -/
theorem p4Q2PZ37ADJ_oneLinkOpenEnergyCap_mass_ge_eighth :
    (1 / 8 : ℝ) ≤ Measure.real μ p4Q2PZ37ADJ_oneLinkOpenEnergyCap :=
  (p4Q2PZ37ABV_lowEnergyCap_real_mass_lower).trans
    (measureReal_mono p4Q2PZ37ADJ_originalLowCap_subset_openEnergyCap)

/-- Genuine quaternion-translated open cap; its measure is unchanged
by the SAME original normalized compact SU(2) Haar probability. -/
def p4Q2PZ37ADJ_translatedOpenEnergyCap (i : Fin 4 × Bool) : Set G :=
  {g | E (p4Q2PZ37ABV_capTranslate i * g) < (3 / 4 : ℝ)}

theorem p4Q2PZ37ADJ_translatedOpenEnergyCap_isOpen (i : Fin 4 × Bool) :
    IsOpen (p4Q2PZ37ADJ_translatedOpenEnergyCap i) := by
  have hTranslate : Continuous
      (fun g : G => p4Q2PZ37ABV_capTranslate i * g) :=
    continuous_const.mul continuous_id
  exact p4Q2PZ37ADJ_oneLinkOpenEnergyCap_isOpen.preimage hTranslate

theorem p4Q2PZ37ADJ_translatedOpenEnergyCap_mass_eq
    (i : Fin 4 × Bool) :
    Measure.real μ (p4Q2PZ37ADJ_translatedOpenEnergyCap i) =
      Measure.real μ p4Q2PZ37ADJ_oneLinkOpenEnergyCap := by
  have hp : MeasurePreserving
      (fun g : G => p4Q2PZ37ABV_capTranslate i * g) μ μ := by
    simpa only [mul_one] using
      (normalizedCompactHaar_measurePreserving_mul_left_right
        G (p4Q2PZ37ABV_capTranslate i) (1 : G))
  change Measure.real μ
      ((fun g : G => p4Q2PZ37ABV_capTranslate i * g) ⁻¹'
        p4Q2PZ37ADJ_oneLinkOpenEnergyCap) =
      Measure.real μ p4Q2PZ37ADJ_oneLinkOpenEnergyCap
  simp only [measureReal_def]
  rw [hp.measure_preimage
    p4Q2PZ37ADJ_oneLinkOpenEnergyCap_isOpen.measurableSet.nullMeasurableSet]

theorem p4Q2PZ37ADJ_translatedOpenEnergyCap_mass_ge_eighth
    (i : Fin 4 × Bool) :
    (1 / 8 : ℝ) ≤ Measure.real μ (p4Q2PZ37ADJ_translatedOpenEnergyCap i) := by
  rw [p4Q2PZ37ADJ_translatedOpenEnergyCap_mass_eq]
  exact p4Q2PZ37ADJ_oneLinkOpenEnergyCap_mass_ge_eighth

/-- ABV's ORIGINAL eight quaternion translations cover every genuine
SU(2) point even with the strict 3/4 relaxed Wilson threshold. -/
theorem p4Q2PZ37ADJ_eight_true_open_caps_cover (g : G) :
    ∃ i : Fin 4 × Bool, g ∈ p4Q2PZ37ADJ_translatedOpenEnergyCap i := by
  have hCover :
      g ∈ (⋃ i : Fin 4 × Bool,
        (fun g : G => p4Q2PZ37ABV_capTranslate i * g) ⁻¹'
          p4Q2PZ37ABV_lowEnergyCap) := by
    rw [p4Q2PZ37ABV_eight_cap_cover]
    exact Set.mem_univ g
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hCover
  refine ⟨i, ?_⟩
  change p4Q2PZ37ABV_capTranslate i * g ∈
    p4Q2PZ37ABV_lowEnergyCap at hi
  exact p4Q2PZ37ADJ_originalLowCap_subset_openEnergyCap hi

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "slice" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local instance p4Q2PZ37ADJ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADJ_sliceProbability : IsProbabilityMeasure slice := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ADJ_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

private theorem p4Q2PZ37ADJ_leftCoordinate_measurePreserving
    (e : Link) :
    MeasurePreserving (fun z : Pair => z.1 e) outer μ := by
  have hLeft : MeasurePreserving (fun z : Pair => z.1) outer slice := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    exact MeasureTheory.measurePreserving_fst
  have hEval : MeasurePreserving (fun x : Cfg => x e) slice μ := by
    simpa only [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure] using
      (MeasureTheory.measurePreserving_eval (fun _ : Link => μ) e)
  simpa only [Function.comp_def] using hEval.comp hLeft

private theorem p4Q2PZ37ADJ_rightCoordinate_measurePreserving
    (e : Link) :
    MeasurePreserving (fun z : Pair => z.2 e) outer μ := by
  have hRight : MeasurePreserving (fun z : Pair => z.2) outer slice := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    exact MeasureTheory.measurePreserving_snd
  have hEval : MeasurePreserving (fun x : Cfg => x e) slice μ := by
    simpa only [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure] using
      (MeasureTheory.measurePreserving_eval (fun _ : Link => μ) e)
  simpa only [Function.comp_def] using hEval.comp hRight

/-- A REAL one-link cylinder in the ORIGINAL H-dependent boundary pair,
not the auxiliary two-copy Haar variable used by ABV. -/
def p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder
    (e : Link) : Set Pair :=
  {z | z.1 e ∈ p4Q2PZ37ADJ_oneLinkOpenEnergyCap}

theorem p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_isOpen
    (e : Link) :
    IsOpen (p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder H e) := by
  have hEval : Continuous (fun z : Pair => z.1 e) :=
    (continuous_apply e).comp continuous_fst
  exact p4Q2PZ37ADJ_oneLinkOpenEnergyCap_isOpen.preimage hEval

/-- Exact original H-dependent pair-Haar mass equals the true SINGLE
SU(2) factor mass, independently of the number of links and H. -/
theorem p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_eq
    (e : Link) :
    Measure.real outer (p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder H e) =
      Measure.real μ p4Q2PZ37ADJ_oneLinkOpenEnergyCap := by
  have hp := p4Q2PZ37ADJ_leftCoordinate_measurePreserving H e
  change Measure.real outer
    ((fun z : Pair => z.1 e) ⁻¹' p4Q2PZ37ADJ_oneLinkOpenEnergyCap) =
    Measure.real μ p4Q2PZ37ADJ_oneLinkOpenEnergyCap
  simp only [measureReal_def]
  rw [hp.measure_preimage
    p4Q2PZ37ADJ_oneLinkOpenEnergyCap_isOpen.measurableSet.nullMeasurableSet]

theorem p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_ge_eighth
    (e : Link) :
    (1 / 8 : ℝ) ≤
      Measure.real outer (p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder H e) := by
  rw [p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_eq]
  exact p4Q2PZ37ADJ_oneLinkOpenEnergyCap_mass_ge_eighth

/-- The ACTUAL original boundary Haar cylinder unconditionally crosses
the ADI NECESSARY 1/17 mass filter, but not the covariance-amplitude test. -/
theorem p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_gt_seventeenth
    (e : Link) :
    (1 / 17 : ℝ) <
      Measure.real outer (p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder H e) := by
  have h := p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_ge_eighth H e
  linarith

/-- ORIGINAL boundary pair-Haar cylinder for an actual quaternion
translated coordinate cap. This changes neither the physical source
nor the original outer Haar probability measure. -/
def p4Q2PZ37ADJ_originalTranslatedFirstCylinder
    (e : Link) (i : Fin 4 × Bool) : Set Pair :=
  {z | z.1 e ∈ p4Q2PZ37ADJ_translatedOpenEnergyCap i}

theorem p4Q2PZ37ADJ_originalTranslatedFirstCylinder_isOpen
    (e : Link) (i : Fin 4 × Bool) :
    IsOpen (p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i) := by
  have hEval : Continuous (fun z : Pair => z.1 e) :=
    (continuous_apply e).comp continuous_fst
  exact (p4Q2PZ37ADJ_translatedOpenEnergyCap_isOpen i).preimage hEval

theorem p4Q2PZ37ADJ_originalTranslatedFirstCylinder_mass_eq
    (e : Link) (i : Fin 4 × Bool) :
    Measure.real outer (p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i) =
      Measure.real μ (p4Q2PZ37ADJ_translatedOpenEnergyCap i) := by
  have hp := p4Q2PZ37ADJ_leftCoordinate_measurePreserving H e
  change Measure.real outer
    ((fun z : Pair => z.1 e) ⁻¹' p4Q2PZ37ADJ_translatedOpenEnergyCap i) =
    Measure.real μ (p4Q2PZ37ADJ_translatedOpenEnergyCap i)
  simp only [measureReal_def]
  rw [hp.measure_preimage
    (p4Q2PZ37ADJ_translatedOpenEnergyCap_isOpen i).measurableSet.nullMeasurableSet]

theorem p4Q2PZ37ADJ_originalTranslatedFirstCylinder_mass_gt_seventeenth
    (e : Link) (i : Fin 4 × Bool) :
    (1 / 17 : ℝ) <
      Measure.real outer (p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i) := by
  rw [p4Q2PZ37ADJ_originalTranslatedFirstCylinder_mass_eq,
    p4Q2PZ37ADJ_translatedOpenEnergyCap_mass_eq]
  have h := p4Q2PZ37ADJ_oneLinkOpenEnergyCap_mass_ge_eighth
  linarith

/-- Eight large-mass open first-boundary cylinders cover the COMPLETE
original H-dependent boundary-pair configuration space, at each link. -/
theorem p4Q2PZ37ADJ_eight_original_boundary_cylinders_cover
    (e : Link) (z : Pair) :
    ∃ i : Fin 4 × Bool,
      z ∈ p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i := by
  obtain ⟨i, hi⟩ := p4Q2PZ37ADJ_eight_true_open_caps_cover (z.1 e)
  exact ⟨i, hi⟩

/-- The genuine centered physical source's ACI covariance witness
belongs to an ACTUAL original H-dependent open Haar region with
numeric mass > 1/17. Covariance is asserted nonzero AT THE WITNESS,
not uniformly large over the entire large region. -/
theorem p4Q2PZ37ADJ_originalEveryLink_nonzeroCovariance_largeCylinder
    (e : Link) :
    ∃ (i : Fin 4 × Bool) (z₀ : Pair),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0 ∧
      z₀ ∈ p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i ∧
      IsOpen (p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i) ∧
      (1 / 17 : ℝ) <
        Measure.real outer (p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i) := by
  obtain ⟨z₀, hz₀⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
      (originalWilsonExplicitIdentityBoundary H)
  obtain ⟨i, hi⟩ :=
    p4Q2PZ37ADJ_eight_original_boundary_cylinders_cover H e z₀
  exact ⟨i, z₀, hz₀, hi,
    p4Q2PZ37ADJ_originalTranslatedFirstCylinder_isOpen H e i,
    p4Q2PZ37ADJ_originalTranslatedFirstCylinder_mass_gt_seventeenth H e i⟩

private theorem p4Q2PZ37ADJ_originalOuterOpenPos :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
    unfold normalizedCompactHaar
    infer_instance
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    infer_instance
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- ACI's nonzero covariance, ACD continuity and the genuine open
cylinder yield an ACTUAL smaller covariance-stable OPEN region,
its strictly positive original Haar mass, and the ADE exact
covariance-square moment lower bound. The >1/17 parent mass is
not incorrectly assigned to the smaller covariance region. -/
theorem p4Q2PZ37ADJ_originalLargeCylinder_hasPositiveCovarianceSubregion
    (e : Link) :
    ∃ (i : Fin 4 × Bool) (A : Set Pair) (a : ℝ),
      IsOpen A ∧
      A ⊆ p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i ∧
      0 < a ∧ 0 < Measure.real outer A ∧
      (1 / 17 : ℝ) <
        Measure.real outer (p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i) ∧
      (∀ z ∈ A, a ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) ∧
      a ^ 2 * Measure.real outer A ≤
        S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨i, z₀, hz₀, hAt, hCylOpen, hCylMass⟩ :=
    p4Q2PZ37ADJ_originalEveryLink_nonzeroCovariance_largeCylinder H e
  let a : ℝ :=
    |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2
  let A : Set Pair :=
    p4Q2PZ37ADJ_originalTranslatedFirstCylinder H e i ∩
      {z | a < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|}
  have hCont : Continuous (fun z : Pair =>
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) :=
    p4Q2PZ37ACD_originalReceiver_covariance_continuous
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e
  have hOpen : IsOpen A :=
    hCylOpen.inter (isOpen_lt continuous_const hCont.abs)
  have ha : 0 < a := div_pos (abs_pos.mpr hz₀) (by norm_num)
  have hAtA : z₀ ∈ A := by
    refine ⟨hAt, ?_⟩
    change a < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀|
    dsimp [a]
    have hPos : 0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| :=
      abs_pos.mpr hz₀
    linarith
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure :=
    p4Q2PZ37ADJ_originalOuterOpenPos H
  have hMass : 0 < Measure.real outer A :=
    ENNReal.toReal_pos ((hOpen.measure_pos outer ⟨z₀, hAtA⟩).ne')
      (measure_ne_top _ _)
  have hFloor : ∀ z ∈ A,
      a ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
    intro z hz
    exact hz.2.le
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e A a hOpen ha hFloor
  refine ⟨i, A, a, hOpen, ?_, ha, hMass, hCylMass, hFloor, hMoment⟩
  intro z hz
  exact hz.1

/-- Two genuine SU(2) boundary coordinates at the SAME spatial link:
the original boundary pair-Haar marginal is precisely the original
auxiliary G×G Haar. The preexisting ABV pair cap lower 1/64
therefore holds on a TRUE physical-boundary pair cylinder. -/
def p4Q2PZ37ADJ_originalTwoBoundaryCoordinateCap
    (e : Link) : Set Pair :=
  (fun z : Pair => (z.1 e, z.2 e)) ⁻¹' p4Q2PZ37ABV_pairCap

theorem p4Q2PZ37ADJ_originalTwoBoundaryCoordinateCap_mass_ge_sixtyFour
    (e : Link) :
    (1 / 64 : ℝ) ≤
      Measure.real outer (p4Q2PZ37ADJ_originalTwoBoundaryCoordinateCap H e) := by
  have hEval : MeasurePreserving (fun x : Cfg => x e) slice μ := by
    simpa only [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure] using
      (MeasureTheory.measurePreserving_eval (fun _ : Link => μ) e)
  have hPair : MeasurePreserving
      (fun z : Pair => (z.1 e, z.2 e)) outer (μ.prod μ) := by
    have hProd := hEval.prod hEval
    simpa [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      Function.comp_def] using hProd
  have hMass :
      Measure.real outer (p4Q2PZ37ADJ_originalTwoBoundaryCoordinateCap H e) =
        Measure.real (μ.prod μ) p4Q2PZ37ABV_pairCap := by
    change Measure.real outer
      ((fun z : Pair => (z.1 e, z.2 e)) ⁻¹' p4Q2PZ37ABV_pairCap) =
      Measure.real (μ.prod μ) p4Q2PZ37ABV_pairCap
    simp only [measureReal_def]
    rw [hPair.measure_preimage p4Q2PZ37ABV_pairCap_measurable.nullMeasurableSet]
  rw [hMass]
  exact p4Q2PZ37ABV_pairCap_real_mass_lower

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADJ_oneLinkOpenEnergyCap_isOpen
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADJ_originalLowCap_subset_openEnergyCap
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADJ_oneLinkOpenEnergyCap_mass_ge_eighth
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADJ_translatedOpenEnergyCap_isOpen
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADJ_translatedOpenEnergyCap_mass_eq
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADJ_translatedOpenEnergyCap_mass_ge_eighth
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADJ_eight_true_open_caps_cover
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_ge_eighth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalFirstBoundaryOpenCylinder_mass_gt_seventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalTranslatedFirstCylinder_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalTranslatedFirstCylinder_mass_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalTranslatedFirstCylinder_mass_gt_seventeenth
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_eight_original_boundary_cylinders_cover
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalEveryLink_nonzeroCovariance_largeCylinder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalLargeCylinder_hasPositiveCovarianceSubregion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADJ_originalTwoBoundaryCoordinateCap_mass_ge_sixtyFour
