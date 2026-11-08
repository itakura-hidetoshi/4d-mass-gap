import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWeightedCubicRemainderV5_PZ37AHY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHZ — original full-action cubic moment from uniform center reflection

Keep the original complete one-slab Wilson action, both spatial halfweights,
the original signed ZW source, original spatial product Haar and all history.
Construct a NEW uniform all-link SU(2) center reflection U(A)(e)=(-I)*A(e).
Unlike AHW's odd-flux cochain, this reflection preserves every spatial
four-edge holonomy, hence W and f, while Cross(U(A),B)=2*p_H-Cross(A,B).

Writing X=Cross-p_H, a=(3*p_H+W(B))/2, the original full action is S=f+a+X.
True Haar transport makes invariant-weight odd centered-crossing moments
vanish. The even term integral f*X^2 is separately cancelled by AHS's
original two-crossing Ward theorem; odd symmetry alone does not remove it.

The genuine third SOURCE-weighted full-ACTION Haar moment is
  M3full(B) = Q4 + (3/4)*(3*p_H+W(B))^2*V_H + 3*D(B),
  Q4 = integral f^4 >= 0, D(B) = integral f^2*X^2 >= 0.
It is strictly positive at every original finite H and boundary B.
AHY's actual cubic source-part correlations satisfy J_+ - J_- = M3full > 0.

This is not the already-zero source moment integral f^3, nor an assertion
about the actual transfer sign at fixed beta. Q4 and D are genuine retained
integrals, not asserted numerically evaluated. No fixed-beta sign shell,
volume-uniform coercivity, Hamiltonian gap or continuum YM gap is claimed.
All previous physical definitions, files, roots, pins and workflows remain.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHZ_center_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHZ_center_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHZ_center_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHZ_center_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHZ_center_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "μ" => normalizedCompactHaar G
local notation "z" => specialUnitaryTwoNegativeIdentity
local notation "s" => p4Q2PZ37AHW_originalCenterSign
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H
local notation "Hol" => periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Jp" => p4Q2PZ37AHY_originalPositiveActionCubeMoment H
local notation "Jm" => p4Q2PZ37AHY_originalNegativeActionCubeMoment H

local instance p4Q2PZ37AHZ_center_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHZ_center_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Uniform, literal left multiplication by the rank-two SU(2) center. -/
def p4Q2PZ37AHZ_originalUniformCenter (A : Cfg) : Cfg :=
  fun e => z * A e

local notation "T" => p4Q2PZ37AHZ_originalUniformCenter H

theorem p4Q2PZ37AHZ_originalUniformCenter_involutive :
    Function.Involutive T := by
  intro A
  funext e
  change z * (z * A e) = A e
  rw [← mul_assoc, p4Q2PZ37AHW_originalCenter_square, one_mul]

/-- AHW's product-Haar argument with the constant center element on all links. -/
theorem p4Q2PZ37AHZ_originalUniformCenter_Haar_measurePreserving :
    MeasurePreserving T muH muH := by
  have hcoord : MeasurePreserving (fun u : G => z * u) μ μ := by
    simpa using
      (normalizedCompactHaar_measurePreserving_mul_left_right G z (1 : G))
  refine ⟨?_, ?_⟩
  · unfold p4Q2PZ37AHZ_originalUniformCenter
    refine measurable_pi_lambda _ ?_
    intro e
    exact hcoord.measurable.comp (measurable_pi_apply e)
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    let F : Link → G → G := fun _ u => z * u
    have hF : ∀ e, AEMeasurable (F e) μ :=
      fun _ => hcoord.measurable.aemeasurable
    letI : ∀ e, SigmaFinite (Measure.map (F e) μ) := fun _ => by
      change SigmaFinite (Measure.map (fun u : G => z * u) μ)
      rw [hcoord.map_eq]
      infer_instance
    rw [show T = (fun A e => F e (A e)) by rfl]
    rw [Measure.pi_map_pi hF]
    congr 1
    funext e
    exact hcoord.map_eq

/-- Four uniform center signs cancel in the ordered spatial holonomy. -/
theorem p4Q2PZ37AHZ_originalPlaquetteHolonomy_uniformCenter
    (p : Plaq) (A : Cfg) :
    Hol (T A) p = Hol A p := by
  change
    (z * A (e0 p)) * (z * A (e1 p)) *
      (z * A (e2 p))⁻¹ * (z * A (e3 p))⁻¹ =
      A (e0 p) * A (e1 p) * (A (e2 p))⁻¹ * (A (e3 p))⁻¹
  rw [p4Q2PV_originalSU2Center_commutes (A (e0 p)),
    p4Q2PV_originalSU2Center_commutes (A (e1 p)),
    p4Q2PV_originalSU2Center_commutes (A (e2 p)),
    p4Q2PV_originalSU2Center_commutes (A (e3 p))]
  rw [← p4Q2PZ37AHW_originalCenterSign_one]
  rw [p4Q2PZ37AHW2_originalCenterSign_inv_mul,
    p4Q2PZ37AHW2_originalCenterSign_inv_mul]
  rw [p4Q2PZ37AHW2_originalCenterSign_interleave,
    p4Q2PZ37AHW2_originalCenterSign_interleave,
    p4Q2PZ37AHW2_originalCenterSign_interleave]
  have hBits : (1 : ZMod 2) + 1 + 1 + 1 = 0 := by decide
  rw [hBits, p4Q2PZ37AHW_originalCenterSign_zero, mul_one]

theorem p4Q2PZ37AHZ_originalSpatialWilson_uniformCenter_invariant
    (A : Cfg) :
    W (T A) = W A := by
  simp only [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction,
    p4Q2PZ37AHZ_originalPlaquetteHolonomy_uniformCenter H]

theorem p4Q2PZ37AHZ_originalSource_uniformCenter_invariant
    (A : Cfg) :
    fCont (T A) = fCont A := by
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H (T A),
    p4Q2PZ37AGN_originalCenteredContinuous_eq H A,
    p4Q2PZ37AHZ_originalSpatialWilson_uniformCenter_invariant H A]

/-- A temporal crossing contains one reflected source link, so it complements. -/
theorem p4Q2PZ37AHZ_originalSingleCrossing_uniformCenter_complement
    (A B : Cfg) (e : Link) :
    E (((T A) e)⁻¹ * B e) = 2 - E ((A e)⁻¹ * B e) := by
  change E ((z * A e)⁻¹ * B e) = 2 - E ((A e)⁻¹ * B e)
  rw [mul_inv_rev, p4Q2PV_originalSU2Center_inverse,
    p4Q2PV_originalSU2Center_move_right,
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]

/-- The exact original link count equals p_H by AHQ; no coordinate estimate. -/
theorem p4Q2PZ37AHZ_originalCrossing_uniformCenter_complement
    (A B : Cfg) :
    Cross (T A) B = 2 * pH - Cross A B := by
  calc
    Cross (T A) B =
        2 * ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) -
          Cross A B := by
      unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
      generalize periodicHypercubicEvenSpatialSliceLinkList H = es
      induction es with
      | nil => simp
      | cons e es ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons,
            Nat.cast_add, Nat.cast_one]
          rw [p4Q2PZ37AHZ_originalSingleCrossing_uniformCenter_complement
            H A B e, ih]
          ring
    _ = 2 * pH - Cross A B := by
      rw [p4Q2PZ37AHQ_crossingLinkCount_exact H]

theorem p4Q2PZ37AHZ_originalCenteredCrossing_uniformCenter_odd
    (A B : Cfg) :
    Cross (T A) B - pH = -(Cross A B - pH) := by
  rw [p4Q2PZ37AHZ_originalCrossing_uniformCenter_complement H A B]
  ring

/-- The exact original centered temporal crossing action. -/
def p4Q2PZ37AHZ_originalCenteredCrossing (A B : Cfg) : ℝ :=
  Cross A B - pH

local notation "X" => p4Q2PZ37AHZ_originalCenteredCrossing H

theorem p4Q2PZ37AHZ_originalCenteredCrossing_continuous (B : Cfg) :
    Continuous (fun A : Cfg => X A B) :=
  (p4Q2PZ37AHP_originalCrossing_continuous H B).sub continuous_const

/-- Both original halfweights are retained in this centered decomposition. -/
theorem p4Q2PZ37AHZ_originalFullAction_centered_decomposition
    (A B : Cfg) :
    S A B = fCont A + (3 * pH + W B) / 2 + X A B := by
  have hSource := p4Q2PZ37AGN_originalCenteredContinuous_eq H A
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    p4Q2PZ37AHZ_originalCenteredCrossing
  linarith only [hSource]

/-- Transport a continuous odd observable through the CONSTRUCTED uniform
center map and the unchanged genuine product Haar measure. -/
theorem p4Q2PZ37AHZ_originalUniformCenter_oddHaar_zero
    (g : Cfg → ℝ) (hg : Continuous g)
    (hOdd : ∀ A : Cfg, g (T A) = -(g A)) :
    (∫ A : Cfg, g A ∂muH) = 0 := by
  have hT := p4Q2PZ37AHZ_originalUniformCenter_Haar_measurePreserving H
  have hMeasMap : AEStronglyMeasurable g (Measure.map T muH) := by
    rw [hT.map_eq]
    exact hg.measurable.aestronglyMeasurable
  have hIntMap :
      (∫ A : Cfg, g (T A) ∂muH) = (∫ A : Cfg, g A ∂muH) := by
    calc
      (∫ A : Cfg, g (T A) ∂muH) =
          ∫ A : Cfg, g A ∂Measure.map T muH := by
        symm
        exact MeasureTheory.integral_map hT.measurable.aemeasurable hMeasMap
      _ = (∫ A : Cfg, g A ∂muH) := by rw [hT.map_eq]
  have hIntOdd :
      (∫ A : Cfg, g (T A) ∂muH) = -(∫ A : Cfg, g A ∂muH) := by
    calc
      (∫ A : Cfg, g (T A) ∂muH) = ∫ A : Cfg, -(g A) ∂muH := by
        apply integral_congr_ae
        filter_upwards with A
        exact hOdd A
      _ = -(∫ A : Cfg, g A ∂muH) := by rw [integral_neg]
  have hEq := hIntMap.symm.trans hIntOdd
  linarith only [hEq]

/-- Any continuous uniform-center-invariant weight is orthogonal to the
original centered crossing. No factorization of Haar correlations is used. -/
theorem p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingHaar_zero
    (g : Cfg → ℝ) (hg : Continuous g)
    (hInv : ∀ A : Cfg, g (T A) = g A) (B : Cfg) :
    (∫ A : Cfg, g A * X A B ∂muH) = 0 := by
  apply p4Q2PZ37AHZ_originalUniformCenter_oddHaar_zero H
    (fun A : Cfg => g A * X A B)
    (hg.mul (p4Q2PZ37AHZ_originalCenteredCrossing_continuous H B))
  intro A
  change g (T A) * (Cross (T A) B - pH) =
    -(g A * (Cross A B - pH))
  rw [hInv A, p4Q2PZ37AHZ_originalCenteredCrossing_uniformCenter_odd H A B]
  ring

/-- The same true symmetry cancels the centered CROSSING cube, including
the original signed source as an invariant weight. -/
theorem p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingCubeHaar_zero
    (g : Cfg → ℝ) (hg : Continuous g)
    (hInv : ∀ A : Cfg, g (T A) = g A) (B : Cfg) :
    (∫ A : Cfg, g A * (X A B) ^ 3 ∂muH) = 0 := by
  apply p4Q2PZ37AHZ_originalUniformCenter_oddHaar_zero H
    (fun A : Cfg => g A * (X A B) ^ 3)
    (hg.mul ((p4Q2PZ37AHZ_originalCenteredCrossing_continuous H B).pow 3))
  intro A
  change g (T A) * (Cross (T A) B - pH) ^ 3 =
    -(g A * (Cross A B - pH) ^ 3)
  rw [hInv A, p4Q2PZ37AHZ_originalCenteredCrossing_uniformCenter_odd H A B]
  ring

theorem p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero
    (n : ℕ) (B : Cfg) :
    (∫ A : Cfg, (fCont A) ^ n * X A B ∂muH) = 0 := by
  apply p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingHaar_zero H
    (fun A : Cfg => (fCont A) ^ n)
    ((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow n)
    (fun A => ?_) B
  change (fCont (T A)) ^ n = (fCont A) ^ n
  rw [p4Q2PZ37AHZ_originalSource_uniformCenter_invariant H A]

theorem p4Q2PZ37AHZ_originalSourcePower_centeredCrossingCubeHaar_zero
    (n : ℕ) (B : Cfg) :
    (∫ A : Cfg, (fCont A) ^ n * (X A B) ^ 3 ∂muH) = 0 := by
  apply p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingCubeHaar_zero H
    (fun A : Cfg => (fCont A) ^ n)
    ((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow n)
    (fun A => ?_) B
  change (fCont (T A)) ^ n = (fCont A) ^ n
  rw [p4Q2PZ37AHZ_originalSource_uniformCenter_invariant H A]

/-- The even centered-crossing square needs AHS's actual two-crossing
Ward cancellation. It does not follow from odd symmetry alone. -/
theorem p4Q2PZ37AHZ_originalSource_centeredCrossingSquareHaar_zero
    (B : Cfg) :
    (∫ A : Cfg, fCont A * (X A B) ^ 2 ∂muH) = 0 := by
  calc
    (∫ A : Cfg, fCont A * (X A B) ^ 2 ∂muH) =
        ∫ A : Cfg, fCont A *
          (pH ^ 2 + (-2 * pH) * Cross A B + 1 * (Cross A B) ^ 2) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      unfold p4Q2PZ37AHZ_originalCenteredCrossing
      ring
    _ = 0 :=
      p4Q2PZ37AHS_originalSource_quadraticCrossingHaar_zero H B
        (pH ^ 2) (-2 * pH) 1

/-- Genuine original source fourth Haar moment, retained as an actual integral. -/
def p4Q2PZ37AHZ_originalSourceFourthHaarMoment : ℝ :=
  ∫ A : Cfg, (fCont A) ^ 4 ∂muH

/-- Genuine nonnegative squared-source/centered-crossing-square correlation. -/
def p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, (fCont A) ^ 2 * (X A B) ^ 2 ∂muH

/-- The actual third SOURCE-weighted full-ACTION moment. This is different
from the already-zero pure source moment integral f^3. -/
def p4Q2PZ37AHZ_originalThirdFullActionHaarMoment (B : Cfg) : ℝ :=
  ∫ A : Cfg, fCont A * (S A B) ^ 3 ∂muH

local notation "Q4" => p4Q2PZ37AHZ_originalSourceFourthHaarMoment H
local notation "D" => p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment H
local notation "M3full" => p4Q2PZ37AHZ_originalThirdFullActionHaarMoment H

theorem p4Q2PZ37AHZ_originalSourceFourthHaarMoment_nonneg :
    0 ≤ Q4 := by
  apply integral_nonneg
  intro A
  positivity

theorem p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment_nonneg
    (B : Cfg) : 0 ≤ D B := by
  exact integral_nonneg (fun A => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Original full cubic integrand is integrable by the already verified AHY API. -/
theorem p4Q2PZ37AHZ_originalThirdFullAction_integrable (B : Cfg) :
    Integrable (fun A : Cfg => fCont A * (S A B) ^ 3) muH :=
  p4Q2PZ37AHY_originalWeightedActionCube_integrable H
    (fun A : Cfg => fCont A) (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous B

/-- Pure integration/algebra step. The actual centered-crossing symmetry
lemmas are supplied as five explicitly typed integral equalities. -/
theorem p4Q2PZ37AHZ_cubicIntegral_of_centeredCancellations
    (xCross : Cfg → ℝ) (hX : Continuous xCross) (a : ℝ) (B : Cfg)
    (hS : ∀ A : Cfg, S A B = fCont A + a + xCross A)
    (h10 : (∫ A : Cfg, fCont A * xCross A ∂muH) = 0)
    (h20 : (∫ A : Cfg, (fCont A) ^ 2 * xCross A ∂muH) = 0)
    (h30 : (∫ A : Cfg, (fCont A) ^ 3 * xCross A ∂muH) = 0)
    (h12 : (∫ A : Cfg, fCont A * (xCross A) ^ 2 ∂muH) = 0)
    (h13 : (∫ A : Cfg, fCont A * (xCross A) ^ 3 ∂muH) = 0) :
    (∫ A : Cfg, fCont A * (S A B) ^ 3 ∂muH) =
      (∫ A : Cfg, (fCont A) ^ 4 ∂muH) + 3 * a ^ 2 * Vsrc +
        3 * (∫ A : Cfg, (fCont A) ^ 2 * (xCross A) ^ 2 ∂muH) := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hInt {g : Cfg → ℝ} (hg : Continuous g) : Integrable g muH :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZero : (∫ A : Cfg, fCont A ∂muH) = 0 :=
    p4Q2PZ37AHP_originalSource_mean_zero H
  have hCubeZero : (∫ A : Cfg, (fCont A) ^ 3 ∂muH) = 0 :=
    p4Q2PZ37AHW2_originalSourceThirdMoment_zero H

  -- The three retained even contributions.
  have i4 : Integrable (fun A : Cfg => (fCont A) ^ 4) muH :=
    hInt (hf.pow 4)
  have iV : Integrable (fun A : Cfg => (3 * a ^ 2) * (fCont A) ^ 2) muH :=
    (hInt (hf.pow 2)).const_mul _
  have iD : Integrable (fun A : Cfg =>
      3 * ((fCont A) ^ 2 * (xCross A) ^ 2)) muH :=
    (hInt ((hf.pow 2).mul (hX.pow 2))).const_mul _
  let main : Cfg → ℝ := fun A =>
    (fCont A) ^ 4 + (3 * a ^ 2) * (fCont A) ^ 2 +
      3 * ((fCont A) ^ 2 * (xCross A) ^ 2)
  have iMain : Integrable main muH := (i4.add iV).add iD
  have hMain : (∫ A : Cfg, main A ∂muH) =
      (∫ A : Cfg, (fCont A) ^ 4 ∂muH) + 3 * a ^ 2 * Vsrc +
        3 * (∫ A : Cfg, (fCont A) ^ 2 * (xCross A) ^ 2 ∂muH) := by
    change (∫ A : Cfg,
      (fCont A) ^ 4 + (3 * a ^ 2) * (fCont A) ^ 2 +
        3 * ((fCont A) ^ 2 * (xCross A) ^ 2) ∂muH) = _
    have hSplit := integral_add (i4.add iV) iD
    simp only [Pi.add_apply] at hSplit
    rw [hSplit, integral_add i4 iV,
      integral_const_mul, integral_const_mul]
    rfl

  -- The seven separately canceled terms, including the even mixed f*xCross².
  have j0 : Integrable (fun A : Cfg => (3 * a) * (fCont A) ^ 3) muH :=
    (hInt (hf.pow 3)).const_mul _
  have j1 : Integrable (fun A : Cfg => 3 * ((fCont A) ^ 3 * xCross A)) muH :=
    (hInt ((hf.pow 3).mul hX)).const_mul _
  have j2 : Integrable (fun A : Cfg => (6 * a) * ((fCont A) ^ 2 * xCross A)) muH :=
    (hInt ((hf.pow 2).mul hX)).const_mul _
  have j3 : Integrable (fun A : Cfg => a ^ 3 * fCont A) muH :=
    (hInt hf).const_mul _
  have j4 : Integrable (fun A : Cfg => (3 * a ^ 2) * (fCont A * xCross A)) muH :=
    (hInt (hf.mul hX)).const_mul _
  have j5 : Integrable (fun A : Cfg => (3 * a) * (fCont A * (xCross A) ^ 2)) muH :=
    (hInt (hf.mul (hX.pow 2))).const_mul _
  have j6 : Integrable (fun A : Cfg => fCont A * (xCross A) ^ 3) muH :=
    hInt (hf.mul (hX.pow 3))
  let vanish : Cfg → ℝ := fun A =>
    (3 * a) * (fCont A) ^ 3 + 3 * ((fCont A) ^ 3 * xCross A) +
      (6 * a) * ((fCont A) ^ 2 * xCross A) + a ^ 3 * fCont A +
      (3 * a ^ 2) * (fCont A * xCross A) +
      (3 * a) * (fCont A * (xCross A) ^ 2) + fCont A * (xCross A) ^ 3
  have iVanish : Integrable vanish muH :=
    (((((j0.add j1).add j2).add j3).add j4).add j5).add j6
  have hVanish : (∫ A : Cfg, vanish A ∂muH) = 0 := by
    change (∫ A : Cfg,
      (3 * a) * (fCont A) ^ 3 + 3 * ((fCont A) ^ 3 * xCross A) +
        (6 * a) * ((fCont A) ^ 2 * xCross A) + a ^ 3 * fCont A +
        (3 * a ^ 2) * (fCont A * xCross A) +
        (3 * a) * (fCont A * (xCross A) ^ 2) + fCont A * (xCross A) ^ 3 ∂muH) = 0
    have hSplit2 := integral_add (j0.add j1) j2
    have hSplit3 := integral_add ((j0.add j1).add j2) j3
    have hSplit4 := integral_add (((j0.add j1).add j2).add j3) j4
    have hSplit5 := integral_add ((((j0.add j1).add j2).add j3).add j4) j5
    have hSplit6 := integral_add (((((j0.add j1).add j2).add j3).add j4).add j5) j6
    simp only [Pi.add_apply] at hSplit2 hSplit3 hSplit4 hSplit5 hSplit6
    rw [hSplit6, hSplit5, hSplit4, hSplit3, hSplit2, integral_add j0 j1]
    simp only [integral_const_mul, hCubeZero, h30, h20, hZero,
      h10, h12, h13, mul_zero, add_zero]

  calc
    (∫ A : Cfg, fCont A * (S A B) ^ 3 ∂muH) =
        ∫ A : Cfg, main A + vanish A ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [hS A]
      dsimp [main, vanish]
      ring
    _ = (∫ A : Cfg, main A ∂muH) + (∫ A : Cfg, vanish A ∂muH) := by
      rw [integral_add iMain iVanish]
    _ = (∫ A : Cfg, (fCont A) ^ 4 ∂muH) + 3 * a ^ 2 * Vsrc +
        3 * (∫ A : Cfg, (fCont A) ^ 2 * (xCross A) ^ 2 ∂muH) := by
      rw [hMain, hVanish, add_zero]


/-- Exact third source-weighted FULL Wilson action moment. All required
cancellations have been proved for the actual model above; none is assumed. -/
theorem p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_exact
    (B : Cfg) :
    M3full B = Q4 + (3 / 4 : ℝ) * (3 * pH + W B) ^ 2 * Vsrc + 3 * D B := by
  have h10 : (∫ A : Cfg, fCont A * X A B ∂muH) = 0 := by
    simpa only [pow_one] using
      p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero H 1 B
  have h13 : (∫ A : Cfg, fCont A * (X A B) ^ 3 ∂muH) = 0 := by
    simpa only [pow_one] using
      p4Q2PZ37AHZ_originalSourcePower_centeredCrossingCubeHaar_zero H 1 B
  have h := p4Q2PZ37AHZ_cubicIntegral_of_centeredCancellations H
    (fun A : Cfg => X A B)
    (p4Q2PZ37AHZ_originalCenteredCrossing_continuous H B)
    ((3 * pH + W B) / 2) B
    (fun A => p4Q2PZ37AHZ_originalFullAction_centered_decomposition H A B)
    h10
    (p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero H 2 B)
    (p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero H 3 B)
    (p4Q2PZ37AHZ_originalSource_centeredCrossingSquareHaar_zero H B)
    h13
  calc
    M3full B =
        (∫ A : Cfg, (fCont A) ^ 4 ∂muH) +
          3 * ((3 * pH + W B) / 2) ^ 2 * Vsrc +
            3 * (∫ A : Cfg, (fCont A) ^ 2 * (X A B) ^ 2 ∂muH) := h
    _ = Q4 + (3 / 4 : ℝ) * (3 * pH + W B) ^ 2 * Vsrc + 3 * D B := by
      unfold p4Q2PZ37AHZ_originalSourceFourthHaarMoment
        p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment
      ring

/-- Explicit finite-volume floor from the retained original variance term. -/
theorem p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_varianceFloor
    (B : Cfg) :
    (3 / 4 : ℝ) * (3 * pH + W B) ^ 2 * Vsrc ≤ M3full B := by
  have hQ := p4Q2PZ37AHZ_originalSourceFourthHaarMoment_nonneg H
  have hD := p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment_nonneg H B
  rw [p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_exact H B]
  linarith only [hQ, hD]

/-- Strict positivity of the genuine FULL-ACTION cubic moment at every
original right boundary. This is not positivity of the signed transfer. -/
theorem p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_pos
    (B : Cfg) : 0 < M3full B := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hv : 0 < Vsrc :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hw : 0 ≤ W B :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) B
  have hc : 0 < 3 * pH + W B := by linarith only [hp, hw]
  have hFloor : 0 < (3 / 4 : ℝ) * (3 * pH + W B) ^ 2 * Vsrc :=
    mul_pos (mul_pos (by norm_num) (pow_pos hc 2)) hv
  exact hFloor.trans_le
    (p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_varianceFloor H B)

/-- AHY's original two source-part correlations differ by this exact
signed full-action moment. The source used by transfer stays unchanged. -/
theorem p4Q2PZ37AHZ_originalSourcePartCubeMoments_sub
    (B : Cfg) : Jp B - Jm B = M3full B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hP := p4Q2PZ37AHY_originalWeightedActionCube_integrable H
    (p4Q2PZ37AHY_originalSourcePositivePart H) hp B
  have hM := p4Q2PZ37AHY_originalWeightedActionCube_integrable H
    (p4Q2PZ37AHY_originalSourceNegativePart H) hm B
  unfold p4Q2PZ37AHY_originalPositiveActionCubeMoment
    p4Q2PZ37AHY_originalNegativeActionCubeMoment
    p4Q2PZ37AHZ_originalThirdFullActionHaarMoment
  rw [← integral_sub hP hM]
  apply integral_congr_ae
  filter_upwards with A
  change ((|fCont A| + fCont A) / 2) * (S A B) ^ 3 -
    ((|fCont A| - fCont A) / 2) * (S A B) ^ 3 =
      fCont A * (S A B) ^ 3
  ring

/-- The true cubic source-part correlations are strictly ordered, even
though their UNWEIGHTED Haar masses are equal by the original mean zero. -/
theorem p4Q2PZ37AHZ_originalSourcePartCubeMoments_strictOrder
    (B : Cfg) : Jm B < Jp B := by
  have hPos := p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_pos H B
  have hSub := p4Q2PZ37AHZ_originalSourcePartCubeMoments_sub H B
  linarith only [hPos, hSub]

/-- The exact positive gap between AHY's two genuine cubic moments has
the same explicit variance floor; it is not a spectral-gap assertion. -/
theorem p4Q2PZ37AHZ_originalSourcePartCubeMoments_varianceSeparation
    (B : Cfg) :
    Jm B + (3 / 4 : ℝ) * (3 * pH + W B) ^ 2 * Vsrc ≤ Jp B := by
  have hFloor := p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_varianceFloor H B
  rw [← p4Q2PZ37AHZ_originalSourcePartCubeMoments_sub H B] at hFloor
  linarith only [hFloor]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalUniformCenter_involutive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalUniformCenter_Haar_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalPlaquetteHolonomy_uniformCenter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSpatialWilson_uniformCenter_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSource_uniformCenter_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSingleCrossing_uniformCenter_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalCrossing_uniformCenter_complement
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalCenteredCrossing_uniformCenter_odd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalCenteredCrossing_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalFullAction_centered_decomposition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalUniformCenter_oddHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalInvariantWeight_centeredCrossingCubeHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSourcePower_centeredCrossingCubeHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSource_centeredCrossingSquareHaar_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSourceFourthHaarMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalThirdFullAction_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_cubicIntegral_of_centeredCancellations
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_varianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalThirdFullActionHaarMoment_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSourcePartCubeMoments_sub
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSourcePartCubeMoments_strictOrder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHZ_originalSourcePartCubeMoments_varianceSeparation
