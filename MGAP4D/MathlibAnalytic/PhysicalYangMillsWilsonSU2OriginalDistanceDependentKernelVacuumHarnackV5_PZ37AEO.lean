import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPerronSharpHaarL2ModulusV5_PZ37AEN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEO — original SU(2) distance-dependent kernel and vacuum Harnack

AEM proves, for the exact original Wilson action, a crossing variation
bounded by one true chord and a spatial variation bounded by 24 chords.
With the symmetric half spatial action, the original slab action changes
by at most 13*d_J under one physical SU(2) link replacement.

Without modifying the Wilson kernel or invoking new regularity axioms,
the exact Boltzmann formula turns this into the TWO-SIDED local estimate

  K_H(A,B_g) <= exp(beta0*(13*d_J(g,h))) * K_H(A,B_h).

The comparison factor tends to one as the actual chordal displacement
tends to zero, unlike AEL's coarse exp(8*beta0) local bound.

The same factor transports to the unchanged continuous physical Perron
vacuum via its EXACT Haar-L2 eigenfunction integral equation and the
nonnegative genuine top eigenvector. No global-action-floor k_H enters
the relative ratio. This result is finite-volume and H-independent at
the ONE-LINK comparison level, not a proof of H-uniform coercivity or
continuum Yang--Mills mass gap.
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

local instance p4Q2PZ37AEO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEO_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEO_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEO_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEO_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

/-- The actual exponential Boltzmann weight has a local multiplicative
Harnack bound whenever the ORIGINAL real action has an absolute modulus. -/
theorem p4Q2PZ37AEO_real_exp_Harnack_of_action_absVariation
    (beta x y delta : ℝ) (hbeta : 0 ≤ beta)
    (hvariation : |x - y| ≤ delta) :
    Real.exp (-beta * x) ≤
      Real.exp (beta * delta) * Real.exp (-beta * y) := by
  have hdelta : y - x ≤ delta := by
    have h := (abs_le.mp hvariation).1
    linarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hdelta hbeta
  have harg : -beta * x ≤ beta * delta + (-beta * y) := by
    nlinarith only [hmul]
  calc
    Real.exp (-beta * x) ≤ Real.exp (beta * delta + (-beta * y)) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp (beta * delta) * Real.exp (-beta * y) :=
      Real.exp_add _ _

/-- Integrate a one-sided multiplicative comparison with a genuine
nonnegative L2 weight. This does NOT require normalization of the weight
or independence of any two boundary variables. -/
theorem p4Q2PZ37AEO_real_nonnegativeWeightedIntegralHarnack
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f u v : α → ℝ) (t : ℝ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hu : Integrable (fun x => f x * u x) μ)
    (hv : Integrable (fun x => f x * v x) μ)
    (huv : ∀ x, u x ≤ t * v x) :
    (∫ x, f x * u x ∂μ) ≤
      t * (∫ x, f x * v x ∂μ) := by
  calc
    (∫ x, f x * u x ∂μ) ≤
        (∫ x, t * (f x * v x) ∂μ) := by
      apply integral_mono_ae hu (hv.const_mul t)
      filter_upwards [hf0] with x hx
      have hprod := mul_le_mul_of_nonneg_left (huv x) hx
      change f x * u x ≤ t * (f x * v x)
      nlinarith only [hprod]
    _ = t * (∫ x, f x * v x ∂μ) :=
      integral_const_mul t _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "Spatial" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Action" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H 2 (by norm_num) b0 hb0
local notation "lambda" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "R" => fun g h : G => Real.exp (b0 * (13 * dJ g h))

local instance p4Q2PZ37AEO_links : Fintype Link := Fintype.ofFinite _

/-- True physical slab action: the crossing link costs at most one chord,
and at most six touching spatial plaquettes cost at most 24 chords in total.
No unproved unique-edge incidence condition is used. -/
theorem p4Q2PZ37AEO_originalSlabAction_oneLinkChordVariation
    (A B : Cfg) (e : Link) (g h : G) :
    |Action A (Replace B e g) - Action A (Replace B e h)| ≤
      13 * dJ g h := by
  let Bg := Replace B e g
  let Bh := Replace B e h
  have hCross :
      |Cross A Bg - Cross A Bh| ≤ dJ g h :=
    p4Q2PZ37AEM_originalTemporalCrossing_oneLinkChordLipschitz H A B e g h
  have hSpatial :
      |Spatial Bg - Spatial Bh| ≤ 24 * dJ g h :=
    p4Q2PZ37AEM_originalSpatialAction_oneLinkChordLipschitz H B e g h
  have heq :
      Action A Bg - Action A Bh =
        (Cross A Bg - Cross A Bh) +
        (1 / 2 : ℝ) * (Spatial Bg - Spatial Bh) := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    ring
  rw [heq]
  calc
    |(Cross A Bg - Cross A Bh) +
      (1 / 2 : ℝ) * (Spatial Bg - Spatial Bh)| ≤
        |Cross A Bg - Cross A Bh| +
          |(1 / 2 : ℝ) * (Spatial Bg - Spatial Bh)| :=
      abs_add_le _ _
    _ = |Cross A Bg - Cross A Bh| +
        (1 / 2 : ℝ) * |Spatial Bg - Spatial Bh| := by
      rw [abs_mul]
      norm_num
    _ ≤ dJ g h + (1 / 2 : ℝ) * (24 * dJ g h) := by
      gcongr
    _ = 13 * dJ g h := by ring

/-- Volume-INDEPENDENT multiplicative one-link Harnack for the original
finite-volume SU(2) Wilson kernel. The factor R(g,h) tends to 1 as g→h
in the genuine normalized real-eight chordal distance. -/
theorem p4Q2PZ37AEO_originalWilsonKernel_oneLinkDistanceHarnack
    (A B : Cfg) (e : Link) (g h : G) :
    K A (Replace B e g) ≤
      R g h * K A (Replace B e h) := by
  have hAction :=
    p4Q2PZ37AEO_originalSlabAction_oneLinkChordVariation H A B e g h
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  exact p4Q2PZ37AEO_real_exp_Harnack_of_action_absVariation
    b0 _ _ (13 * dJ g h) hb0 hAction

/-- The same genuine kernel inequality with source and target link
holonomies interchanged. -/
theorem p4Q2PZ37AEO_originalWilsonKernel_oneLinkDistanceReverse
    (A B : Cfg) (e : Link) (g h : G) :
    K A (Replace B e h) ≤
      R g h * K A (Replace B e g) := by
  have hs := p4Q2PZ37AEO_originalWilsonKernel_oneLinkDistanceHarnack
    H A B e h g
  change K A (Replace B e h) ≤
    Real.exp (b0 * (13 * dJ h g)) * K A (Replace B e g) at hs
  rw [p4Q2PZ37ADK_trueChordalDistance_symm h g] at hs
  exact hs

/-- The comparison factor equals one when there is no link displacement. -/
theorem p4Q2PZ37AEO_originalDistanceHarnackFactor_self (g : G) :
    R g g = 1 := by
  change Real.exp (b0 * (13 * dJ g g)) = 1
  rw [p4Q2PZ37ADK_trueChordalDistance_self]
  simp

/-- The EXACT physical continuous Perron vacuum inherits the
distance-dependent Harnack factor through the original nonnegative
Haar-L2 eigenvector and the pointwise Wilson eigenvalue equation.
No global k_H floor, alternative vacuum, or independence enters. -/
theorem p4Q2PZ37AEO_originalContinuousVacuum_oneLinkDistanceHarnack
    (B : Cfg) (e : Link) (g h : G) :
    Omega (Replace B e g) ≤
      R g h * Omega (Replace B e h) := by
  let μ : Measure Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) b0 hb0
  let Bg := Replace B e g
  let Bh := Replace B e h
  let t : ℝ := R g h
  have hLpos : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0
  have hf0 : ∀ᵐ A ∂μ, 0 ≤ V.1 A := by
    simpa only [V, μ] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
        H 2 (by norm_num) b0 hb0)
  have hInt (D : Cfg) :
      Integrable (fun A : Cfg => V.1 A * K A D) μ := by
    simpa only [V, μ] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_mul_integrable
        H 2 (by norm_num) b0 hb0
        ((V : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2 μ) D)
  have hPerron (D : Cfg) :
      lambda * Omega D = ∫ A : Cfg, V.1 A * K A D ∂μ := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel
        H 2 (by norm_num) b0 hb0 D
  have hIntegral :
      (∫ A : Cfg, V.1 A * K A Bg ∂μ) ≤
        t * (∫ A : Cfg, V.1 A * K A Bh ∂μ) := by
    apply p4Q2PZ37AEO_real_nonnegativeWeightedIntegralHarnack
      μ (fun A : Cfg => V.1 A) (fun A => K A Bg) (fun A => K A Bh)
      t hf0 (hInt Bg) (hInt Bh)
    intro A
    exact p4Q2PZ37AEO_originalWilsonKernel_oneLinkDistanceHarnack H A B e g h
  have hScaled :
      lambda * Omega Bg ≤ lambda * (t * Omega Bh) := by
    calc
      lambda * Omega Bg =
          (∫ A : Cfg, V.1 A * K A Bg ∂μ) := hPerron Bg
      _ ≤ t * (∫ A : Cfg, V.1 A * K A Bh ∂μ) := hIntegral
      _ = t * (lambda * Omega Bh) := by rw [hPerron Bh]
      _ = lambda * (t * Omega Bh) := by ring
  change Omega Bg ≤ t * Omega Bh
  by_contra hcontra
  have hlt : t * Omega Bh < Omega Bg := lt_of_not_ge hcontra
  have hstrict := mul_lt_mul_of_pos_left hlt hLpos
  exact (not_lt_of_ge hScaled) hstrict

/-- Reverse physical Perron comparison at the SAME small-distance factor. -/
theorem p4Q2PZ37AEO_originalContinuousVacuum_oneLinkDistanceReverse
    (B : Cfg) (e : Link) (g h : G) :
    Omega (Replace B e h) ≤
      R g h * Omega (Replace B e g) := by
  have hs := p4Q2PZ37AEO_originalContinuousVacuum_oneLinkDistanceHarnack
    H B e h g
  change Omega (Replace B e h) ≤
    Real.exp (b0 * (13 * dJ h g)) * Omega (Replace B e g) at hs
  rw [p4Q2PZ37ADK_trueChordalDistance_symm h g] at hs
  exact hs

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEO_real_exp_Harnack_of_action_absVariation
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEO_real_nonnegativeWeightedIntegralHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalSlabAction_oneLinkChordVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalWilsonKernel_oneLinkDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalWilsonKernel_oneLinkDistanceReverse
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalDistanceHarnackFactor_self
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalContinuousVacuum_oneLinkDistanceHarnack
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEO_originalContinuousVacuum_oneLinkDistanceReverse
