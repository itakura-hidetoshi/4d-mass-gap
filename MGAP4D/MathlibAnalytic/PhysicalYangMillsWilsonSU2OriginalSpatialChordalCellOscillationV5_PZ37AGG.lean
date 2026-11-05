import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAutomaticSpatialHaarOscillationV5_PZ37AGF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverLocalToGlobalChordalV5_PZ37AET
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGG — original spatial SU(2) chordal oscillation and Haar cells

The actual AEM Wilson spatial action has one-link chordal slope 24.
Its original symmetric one-slab kernel has one-link slope 13*beta0.
Finite-coordinate telescoping therefore gives, for the genuine original
AFZ continuous centered source and AGE signed integrand,

  |f_c(A)-f_c(C)| <= 12*D_sp(A,C),
  |K(A,B)-K(C,B)| <= 13*beta0*D_sp(A,C),
  |g_B(A)-g_B(C)| <= L_H*D_sp(A,C),

where D_sp is the sum of the ACTUAL ADK SU(2) link chordal distances,
and L_H = 6*(1-k_H) + 13*beta0*p_H. No independent regularity premise
or replacement physical model enters.

AGE proves each point of an actual AGD AFQ 24-center spatial Haar product
cell has original per-link radius 4/5. Hence an unconditional geometrical
AGE oscillation budget L_H*(4/5)*|Link_H| exists. We also retain AGF's
global (1-k_H)*p_H bound by taking their minimum: tightening only.

This bounds the genuine signed original transfer around AGE's rational
center quadrature, but neither computes rational center samples nor
certifies a nonzero true transfer sign, two-sign shell, coercivity,
Hamiltonian gap or four-dimensional continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Additive one-coordinate chordal descent for a signed real observable.
Uses the proven AEP finite-coordinate exponential telescoping and AET's
signed exponential comparison, not an assumed regularity theorem. -/
theorem p4Q2PZ37AGG_finiteCoordinate_absLipschitz
    {ι G : Type*} [Fintype ι] [DecidableEq ι]
    (d : G → G → ℝ) (hdSym : ∀ g h, d g h = d h g)
    (L : ℝ) (f : (ι → G) → ℝ)
    (hLocal : ∀ (u : ι → G) (i : ι) (g h : G),
      |f (Function.update u i g) -
        f (Function.update u i h)| ≤ L * d g h)
    (a b : ι → G) :
    |f a-f b| ≤ L * ∑ i : ι, d (a i) (b i) := by
  have hExpLocal :
      ∀ (u : ι → G) (i : ι) (g h : G),
        Real.exp (f (Function.update u i g)) ≤
          Real.exp (L * d g h) *
            Real.exp (f (Function.update u i h)) := by
    intro u i g h
    exact p4Q2PZ37AET_realExpHarnack_of_absDifference
      _ _ _ (hLocal u i g h)
  have hUpper (u v : ι → G) :
      f u-f v ≤ L * ∑ i : ι, d (u i) (v i) := by
    have hx :=
      p4Q2PZ37AEP_finiteCoordinateHarnack d L
        (fun w : ι → G => Real.exp (f w)) hExpLocal u v
    have hExp :
        Real.exp (f u) ≤
          Real.exp (L * ∑ i : ι, d (u i) (v i) + f v) := by
      rw [Real.exp_add]
      exact hx
    have hLe := Real.exp_le_exp.mp hExp
    linarith only [hLe]
  have hForward := hUpper a b
  have hBackward := hUpper b a
  have hSym :
      (∑ i : ι, d (b i) (a i)) =
        ∑ i : ι, d (a i) (b i) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hdSym (b i) (a i)]
  rw [hSym] at hBackward
  apply abs_le.mpr
  constructor
  · linarith only [hBackward]
  · exact hForward

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGG_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGG_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGG_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGG_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "Wc" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "mH" => p4Q2PZ37AFZ_originalWilsonMean H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H
local notation "CellIndex" =>
  Fin (Fintype.card (p4Q2PZ37AGD_spatialGridIndex H))

local instance p4Q2PZ37AGG_links : Fintype Link := Fintype.ofFinite _

/-- Literal spatial-slice all-link distance, using actual ADK SU(2)
chords rather than a new surrogate metric. -/
def p4Q2PZ37AGG_originalSpatialChordalDistance
    (A C : Cfg) : ℝ :=
  ∑ e : Link, dJ (A e) (C e)

theorem p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg
    (A C : Cfg) :
    0 ≤ p4Q2PZ37AGG_originalSpatialChordalDistance H A C := by
  unfold p4Q2PZ37AGG_originalSpatialChordalDistance
  apply Finset.sum_nonneg
  intro e _he
  exact p4Q2PZ37ADK_trueChordalDistance_nonneg (A e) (C e)

/-- Unconditional original centered spatial Wilson source one-link
variation; subtraction of the true Haar mean cancels exactly. -/
theorem p4Q2PZ37AGG_originalCenteredSource_oneLinkChordalSlope
    (A : Cfg) (e : Link) (g h : G) :
    |fCont (Replace A e g) - fCont (Replace A e h)| ≤
      12 * dJ g h := by
  have hW :
      |Wc (Replace A e g) - Wc (Replace A e h)| ≤
        24 * dJ g h :=
    p4Q2PZ37AEM_originalSpatialAction_oneLinkChordLipschitz
      H A e g h
  have hHalf :=
    mul_le_mul_of_nonneg_left hW (by norm_num : (0 : ℝ) ≤ 1 / 2)
  change |(1 / 2 : ℝ) * (Wc (Replace A e g) - mH * 1) -
    (1 / 2 : ℝ) * (Wc (Replace A e h) - mH * 1)| ≤
      12 * dJ g h
  calc
    |(1 / 2 : ℝ) * (Wc (Replace A e g) - mH * 1) -
        (1 / 2 : ℝ) * (Wc (Replace A e h) - mH * 1)| =
      |(1 / 2 : ℝ) * (Wc (Replace A e g) - Wc (Replace A e h))| := by
        congr 1
        ring
    _ = (1 / 2 : ℝ) * |Wc (Replace A e g) - Wc (Replace A e h)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2 : ℝ) * (24 * dJ g h) := hHalf
    _ = 12 * dJ g h := by ring

/-- The genuine original centered source has full spatial
l1 SU(2) chordal slope 12, for every finite H. -/
theorem p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope
    (A C : Cfg) :
    |fCont A - fCont C| ≤
      12 * p4Q2PZ37AGG_originalSpatialChordalDistance H A C := by
  classical
  have hLocal : ∀ (u : Cfg) (i : Link) (g h : G),
      |fCont (Function.update u i g) -
        fCont (Function.update u i h)| ≤ 12 * dJ g h := by
    intro u i g h
    simpa only [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
      using p4Q2PZ37AGG_originalCenteredSource_oneLinkChordalSlope H u i g h
  exact p4Q2PZ37AGG_finiteCoordinate_absLipschitz
    dJ p4Q2PZ37ADK_trueChordalDistance_symm 12
    (fun u : Cfg => fCont u) hLocal A C

/-- Symmetry of the actual one-slab kernel turns AEM's right-coordinate
modulus into a left-coordinate modulus, with unchanged beta0. -/
theorem p4Q2PZ37AGG_originalKernel_leftOneLinkChordalSlope
    (A B : Cfg) (e : Link) (g h : G) :
    |K (Replace A e g) B - K (Replace A e h) B| ≤
      (13 * b0) * dJ g h := by
  calc
    |K (Replace A e g) B - K (Replace A e h) B| =
      |K B (Replace A e g) - K B (Replace A e h)| := by
        rw [
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
            H 2 (by norm_num) b0 p4Q2PZ37ADC_fixedCoupling_pos.le _ B,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
            H 2 (by norm_num) b0 p4Q2PZ37ADC_fixedCoupling_pos.le _ B]
    _ ≤ (13 * b0) * dJ g h :=
      p4Q2PZ37AEM_originalOneSlabKernel_unconditionalChordLipschitz
        H B A e g h

/-- Original one-slab kernel in its spatial integration argument:
an actual global (not just local) geometric Lipschitz certificate. -/
theorem p4Q2PZ37AGG_originalKernel_leftAllLinkChordalSlope
    (B A C : Cfg) :
    |K A B - K C B| ≤
      (13 * b0) * p4Q2PZ37AGG_originalSpatialChordalDistance H A C := by
  classical
  have hLocal : ∀ (u : Cfg) (i : Link) (g h : G),
      |K (Function.update u i g) B -
        K (Function.update u i h) B| ≤ (13 * b0) * dJ g h := by
    intro u i g h
    simpa only [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
      using p4Q2PZ37AGG_originalKernel_leftOneLinkChordalSlope H u B i g h
  exact p4Q2PZ37AGG_finiteCoordinate_absLipschitz
    dJ p4Q2PZ37ADK_trueChordalDistance_symm (13 * b0)
    (fun u : Cfg => K u B) hLocal A C

/-- Explicit authentic fixed-volume signed centered Wilson integrand
slope. Equivalently 6*(1-k_H) + 13*beta0*p_H. -/
def p4Q2PZ37AGG_originalSpatialSlope : ℝ :=
  12 * ((1 - kFloor) / 2) + pH * (13 * b0)

theorem p4Q2PZ37AGG_originalSpatialSlope_nonneg :
    0 ≤ p4Q2PZ37AGG_originalSpatialSlope H := by
  have hr : 0 ≤ (1 - kFloor) / 2 :=
    p4Q2PZ37AGB_originalKernel_radius_nonneg H
  have hp : 0 ≤ pH := p4Q2PZ37AGF_plaquetteCount_nonneg H
  have hb : 0 ≤ b0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  unfold p4Q2PZ37AGG_originalSpatialSlope
  positivity

/-- The true AGE continuous integrand satisfies an unconditional,
distance-vanishing signed variation estimate on all original spatial
configurations; the source is NOT evaluated as an arbitrary L2 value. -/
theorem p4Q2PZ37AGG_originalContinuousIntegrand_allLinkChordalSlope
    (B A C : Cfg) :
    |gCont B A - gCont B C| ≤
      p4Q2PZ37AGG_originalSpatialSlope H *
        p4Q2PZ37AGG_originalSpatialChordalDistance H A C := by
  let D := p4Q2PZ37AGG_originalSpatialChordalDistance H A C
  let r := (1 - kFloor) / 2
  have hd : 0 ≤ D :=
    p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg H A C
  have hSrc : |fCont A - fCont C| ≤ 12 * D :=
    p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope H A C
  have hKer : |K A B - K C B| ≤ (13 * b0) * D :=
    p4Q2PZ37AGG_originalKernel_leftAllLinkChordalSlope H B A C
  have hMid : |K A B - (1 + kFloor) / 2| ≤ r :=
    p4Q2PZ37AGB_originalKernel_centeredMidpointBound H A B
  have hSrcMax : |fCont C| ≤ pH :=
    p4Q2PZ37AGF_originalContinuousSource_abs_le H C
  have h0 : 0 ≤ 12 * D := by positivity
  have hp : 0 ≤ pH := p4Q2PZ37AGF_plaquetteCount_nonneg H
  change |fCont A * (K A B - (1 + kFloor) / 2) -
    fCont C * (K C B - (1 + kFloor) / 2)| ≤
      (12 * ((1 - kFloor) / 2) + pH * (13 * b0)) * D
  calc
    |fCont A * (K A B - (1 + kFloor) / 2) -
        fCont C * (K C B - (1 + kFloor) / 2)| =
      |(fCont A - fCont C) * (K A B - (1 + kFloor) / 2) +
        fCont C * (K A B - K C B)| := by
          congr 1
          ring
    _ ≤ |fCont A - fCont C| * |K A B - (1 + kFloor) / 2| +
        |fCont C| * |K A B - K C B| := by
          calc
            |(fCont A - fCont C) * (K A B - (1 + kFloor) / 2) +
                fCont C * (K A B - K C B)| ≤
              |(fCont A - fCont C) * (K A B - (1 + kFloor) / 2)| +
                |fCont C * (K A B - K C B)| := abs_add_le _ _
            _ = |fCont A - fCont C| * |K A B - (1 + kFloor) / 2| +
                |fCont C| * |K A B - K C B| := by
                  rw [abs_mul, abs_mul]
    _ ≤ (12 * D) * r + pH * ((13 * b0) * D) := by
          exact add_le_add
            (mul_le_mul hSrc hMid (abs_nonneg _) h0)
            (mul_le_mul hSrcMax hKer (abs_nonneg _) hp)
    _ = (12 * ((1 - kFloor) / 2) + pH * (13 * b0)) * D := by
          dsimp [r]
          ring

/-- The real radius of an original 24^Link AFQ product Haar cell,
as certified by the exact AGE chordal bound 4/5 per link. -/
def p4Q2PZ37AGG_originalCellChordalRadius : ℝ :=
  (4 / 5 : ℝ) * (Fintype.card Link : ℝ)

theorem p4Q2PZ37AGG_originalCellChordalRadius_nonneg :
    0 ≤ p4Q2PZ37AGG_originalCellChordalRadius H := by
  unfold p4Q2PZ37AGG_originalCellChordalRadius
  positivity

theorem p4Q2PZ37AGG_originalCell_spatialDistance_le
    (i : CellIndex) (A : Cfg)
    (hA : A ∈ (p4Q2PZ37AGD_toAGCOriginalHaarCells H).cell i) :
    p4Q2PZ37AGG_originalSpatialChordalDistance H A
      (p4Q2PZ37AGE_spatialProductCenter H i) ≤
        p4Q2PZ37AGG_originalCellChordalRadius H := by
  unfold p4Q2PZ37AGG_originalSpatialChordalDistance
  calc
    (∑ e : Link,
        dJ (A e) (p4Q2PZ37AGE_spatialProductCenter H i e)) ≤
      ∑ _e : Link, (4 / 5 : ℝ) := by
        apply Finset.sum_le_sum
        intro e _he
        exact p4Q2PZ37AGE_cell_perLink_chordalRadius H i A hA e
    _ = p4Q2PZ37AGG_originalCellChordalRadius H := by
          simp [p4Q2PZ37AGG_originalCellChordalRadius, mul_comm]

/-- Unconditional physical AGE cellwise oscillation from original
one-link Wilson geometry, rather than AGF's global value range. -/
def p4Q2PZ37AGG_unconditionalGeometricOscillation
    (B : Cfg) :
    p4Q2PZ37AGE_originalSpatialOscillation H B where
  epsilon := p4Q2PZ37AGG_originalSpatialSlope H *
    p4Q2PZ37AGG_originalCellChordalRadius H
  epsilon_nonneg :=
    mul_nonneg
      (p4Q2PZ37AGG_originalSpatialSlope_nonneg H)
      (p4Q2PZ37AGG_originalCellChordalRadius_nonneg H)
  hOsc := by
    intro i A hA
    have hSlope :=
      p4Q2PZ37AGG_originalContinuousIntegrand_allLinkChordalSlope H B A
        (p4Q2PZ37AGE_spatialProductCenter H i)
    have hDist := p4Q2PZ37AGG_originalCell_spatialDistance_le H i A hA
    exact hSlope.trans
      (mul_le_mul_of_nonneg_left hDist
        (p4Q2PZ37AGG_originalSpatialSlope_nonneg H))

/-- Never replace the stronger of two proved bounds by the weaker:
the actual global floor envelope and genuine spatial chordal radius
are combined as a minimum, without any new external premise. -/
def p4Q2PZ37AGG_unconditionalHybridOscillation
    (B : Cfg) :
    p4Q2PZ37AGE_originalSpatialOscillation H B where
  epsilon := min
    (pH * (1 - kFloor))
    (p4Q2PZ37AGG_originalSpatialSlope H *
      p4Q2PZ37AGG_originalCellChordalRadius H)
  epsilon_nonneg := by
    have hg :=
      (p4Q2PZ37AGF_unconditionalFloorOscillation H B).epsilon_nonneg
    have hc :=
      (p4Q2PZ37AGG_unconditionalGeometricOscillation H B).epsilon_nonneg
    exact le_min hg hc
  hOsc := by
    intro i A hA
    apply le_min
    · exact (p4Q2PZ37AGF_unconditionalFloorOscillation H B).hOsc i A hA
    · exact (p4Q2PZ37AGG_unconditionalGeometricOscillation H B).hOsc i A hA

/-- Genuine signed original transfer quadrature with a geometry-aware,
unconditionally proved minimum of the two Wilson oscillation budgets. -/
theorem p4Q2PZ37AGG_originalSignedTransfer_geometryAwareAccuracy
    (B : Cfg) :
    |decomposableOneSliceTransferIntegral H 2 b0
      (p4Q2PZ37ZW_originalCenteredPhysicalDirection H) B -
      (p4Q2PZ37AGC_HaarCenter (p4Q2PZ37AGD_toAGCOriginalHaarCells H)
        (p4Q2PZ37AGE_originalSpatialSample H B) : ℝ)| ≤
      p4Q2PZ37AGC_HaarTotalError (p4Q2PZ37AGD_toAGCOriginalHaarCells H)
        (p4Q2PZ37AGE_originalSpatialSample H B)
        ((p4Q2PZ37AGG_unconditionalHybridOscillation H B).epsilon +
          (1 / 64 : ℝ)) :=
  p4Q2PZ37AGE_originalSignedTransfer_accuracy H B
    (p4Q2PZ37AGG_unconditionalHybridOscillation H B)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGG_finiteCoordinate_absLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalCenteredSource_oneLinkChordalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalKernel_leftOneLinkChordalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalKernel_leftAllLinkChordalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalSpatialSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalContinuousIntegrand_allLinkChordalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalCellChordalRadius_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalCell_spatialDistance_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_unconditionalGeometricOscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_unconditionalHybridOscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGG_originalSignedTransfer_geometryAwareAccuracy
