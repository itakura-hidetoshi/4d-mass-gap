import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPlaquetteCenterTraceV5_PV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NativeTopFirstSlopeV5_PZ37ANU
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPrimaryPlaquetteHaarCharacterBridgeV5_PZ37AMB
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectorySpecialUnitaryTwoStapleOscillationSeparationBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPlaquetteOverlapBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSharedPlaquetteUniqueness
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANV — native first Wilson Haar action moment evaluation

This is the additive research leaf for the ORIGINAL SU(2) one-slab first
Haar-action moment defined in ANU.  The starting step transfers the exact
SU(2) fundamental-character first and second Haar moments to the unchanged
physical time-zero spatial-slice measure, without replacing it with the
reflection-fixed OS boundary or postulating independent plaquettes.

The intended next steps use the actual finite spatial plaquette sum and
temporal crossing action to compute ANU's original first Haar moment.
Unfinished steps are not presented as certified Lean theorems.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "nu" => normalizedCompactHaar G
local notation "Chi" =>
  p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37ANV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANV_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The genuinely physical time-zero PRIMARY spatial plaquette holonomy
has exactly normalized compact SU(2) Haar as its pushforward law.
This is the original four-link spatial-slice Haar, not an assumed OS
measure or a new independent group variable. -/
theorem p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport
    (H : ℕ) (f : G → ℝ) (hf : AEStronglyMeasurable f nu) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      f (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      (∫ g : G, f g ∂nu) := by
  let phi := p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  have hmp : MeasurePreserving phi mu nu :=
    p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2
  have hfmap : AEStronglyMeasurable f (Measure.map phi mu) := by
    rw [hmp.map_eq]
    exact hf
  calc
    _ = ∫ g : G, f g ∂Measure.map phi mu :=
      (MeasureTheory.integral_map hmp.measurable.aemeasurable hfmap).symm
    _ = ∫ g : G, f g ∂nu := by rw [hmp.map_eq]

/-- First moment of the ACTUAL primary spatial plaquette's real normalized
fundamental SU(2) character is exactly zero at every finite physical H. -/
theorem p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero (H : ℕ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  have hf : AEStronglyMeasurable Chi nu :=
    GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.measurable.aestronglyMeasurable
  calc
    _ = ∫ g : G, Chi g ∂nu :=
      p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport H Chi hf
    _ = 0 :=
      GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero

/-- Genuine native four-link SU(2) spatial-slice character has exact
Haar variance 1/4, not an assumed unit variance. -/
theorem p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarSecondMoment (H : ℕ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      (Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) ^ 2
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      (1 / 4 : ℝ) := by
  have hf : AEStronglyMeasurable (fun g : G => (Chi g) ^ 2) nu :=
    (GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.pow 2).measurable.aestronglyMeasurable
  calc
    _ = ∫ g : G, (Chi g) ^ 2 ∂nu :=
      p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport
        H (fun g : G => (Chi g) ^ 2) hf
    _ = (1 / 4 : ℝ) :=
      GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment


/-- True native time-zero spatial primary Wilson ENERGY against its own
fundamental Haar character.  This is exactly -1/4, not a standalone
independence premise about other spatial plaquettes.  The original
Wilson energy E=1-chi and genuine SU(2) Haar variance are unchanged. -/
theorem p4Q2PZ37ANV_originalTimeZeroPrimaryEnergyCharacter_haarPairing
    (H : ℕ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      specialUnitaryWilsonPlaquetteEnergy 2
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      -(1 / 4 : ℝ) := by
  have hChiCont : Continuous Chi :=
    GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous
  have hPairCont : Continuous
      (fun g : G => specialUnitaryWilsonPlaquetteEnergy 2 g * Chi g) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).mul hChiCont
  have hIntChi : Integrable Chi nu :=
    hChiCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hIntChi2 : Integrable (fun g : G => (Chi g)^2) nu :=
    (hChiCont.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (g : G) :
      specialUnitaryWilsonPlaquetteEnergy 2 g * Chi g =
        Chi g - (Chi g)^2 := by
    dsimp [p4Q2PZ35C_originalOneLinkCharacter]
    ring
  calc
    _ = ∫ g : G, specialUnitaryWilsonPlaquetteEnergy 2 g * Chi g ∂nu :=
      p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport
        H _ hPairCont.measurable.aestronglyMeasurable
    _ = ∫ g : G, Chi g - (Chi g)^2 ∂nu := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact hPoint g
    _ = (∫ g : G, Chi g ∂nu) -
        (∫ g : G, (Chi g)^2 ∂nu) :=
      integral_sub hIntChi hIntChi2
    _ = -(1 / 4 : ℝ) := by
      rw [GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero,
        GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment]
      ring


/-- Use the ORIGINAL normalized compact Haar of SU(2) for every physical
single-link relative Wilson factor.  No independent-plaquette
factorization is involved. -/
local instance p4Q2PZ37ANV_haarProbability : IsProbabilityMeasure nu :=
  normalizedCompactHaar_isProbabilityMeasure G

local instance p4Q2PZ37ANV_haarInvariant :
    Measure.IsHaarMeasure nu := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- At zero coupling, the genuine SU(2) relative-link Wilson ENERGY
has Haar mean precisely one, independently of its fixed left endpoint.
This follows from the actual normalized character's Haar mean zero. -/
theorem p4Q2PZ37ANV_originalRelativeLinkEnergy_haarMean_one (a : G) :
    (∫ b : G, specialUnitaryWilsonPlaquetteEnergy 2 (a⁻¹ * b) ∂nu) =
      (1 : ℝ) := by
  have hChiCont : Continuous Chi :=
    GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous
  have hChiInt : Integrable Chi nu :=
    hChiCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEnergyEq (g : G) :
      specialUnitaryWilsonPlaquetteEnergy 2 g = (1 : ℝ) - Chi g := by
    dsimp [p4Q2PZ35C_originalOneLinkCharacter]
    ring
  have hEnergyMean :
      (∫ g : G, specialUnitaryWilsonPlaquetteEnergy 2 g ∂nu) = (1 : ℝ) := by
    calc
      _ = ∫ g : G, (1 : ℝ) - Chi g ∂nu := by
        apply integral_congr_ae
        filter_upwards [] with g
        exact hEnergyEq g
      _ = (∫ _g : G, (1 : ℝ) ∂nu) -
          (∫ g : G, Chi g ∂nu) :=
        integral_sub (integrable_const _) hChiInt
      _ = 1 := by
        rw [GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero]
        simp
  calc
    _ = ∫ g : G, specialUnitaryWilsonPlaquetteEnergy 2 g ∂nu :=
      integral_mul_left_eq_self (μ := nu)
        (specialUnitaryWilsonPlaquetteEnergy 2) a⁻¹
    _ = 1 := hEnergyMean

/-- The exact ORIGINAL finite-link temporal crossing action has a fixed
normalized spatial-slice Haar expectation in its RIGHT boundary, for
every first boundary A. The expectation equals the actual number of
physical spatial links, not a new abstract normalization. -/
theorem p4Q2PZ37ANV_originalCrossingAction_rightHaarMean
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) := by
  classical
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let E := specialUnitaryWilsonPlaquetteEnergy 2
  have hMeasure : muH = Measure.pi (fun _ : Link => nu) := by
    change periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 =
      Measure.pi (fun _ : Link => nu)
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    exact congrArg
      (fun i : Fintype Link =>
        letI : Fintype Link := i
        Measure.pi (fun _ : Link => nu))
      (Subsingleton.elim
        (oneSlabHaarL2SpatialLinkFintype H)
        (inferInstance : Fintype Link))
  have hAction (B : Cfg) :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B =
        ∑ e : Link, E ((A e)⁻¹ * B e) := by
    simp only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction,
      periodicHypercubicEvenSpatialSliceLinkList, Finset.sum_map_toList, E]
    -- The canonical list and this leaf's local finite instance enumerate
    -- the same type; the Finset.univ terms need extensionality.
    apply Finset.sum_congr
    · ext e
      simp
    · intro e _
      rfl
  have hContinuous (e : Link) :
      Continuous (fun b : G => E ((A e)⁻¹ * b)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      (continuous_const.mul continuous_id)
  have hIntegrable (e : Link) :
      Integrable (fun b : G => E ((A e)⁻¹ * b)) nu :=
    (hContinuous e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPiIntegrable (e : Link) :
      Integrable (fun B : Cfg => E ((A e)⁻¹ * B e))
        (Measure.pi (fun _ : Link => nu)) := by
    exact MeasureTheory.integrable_comp_eval
      (μ := fun _ : Link => nu) (i := e) (hIntegrable e)
  have hCoordinateIntegral (e : Link) :
      (∫ B : Cfg, E ((A e)⁻¹ * B e)
          ∂(Measure.pi (fun _ : Link => nu))) =
        (∫ b : G, E ((A e)⁻¹ * b) ∂nu) := by
    exact MeasureTheory.integral_comp_eval
      (μ := fun _ : Link => nu) (i := e)
      (hContinuous e).measurable.aestronglyMeasurable
  calc
    (∫ B : Cfg,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B
        ∂muH) =
        (∫ B : Cfg, ∑ e : Link, E ((A e)⁻¹ * B e)
          ∂(Measure.pi (fun _ : Link => nu))) := by
      rw [hMeasure]
      apply integral_congr_ae
      filter_upwards [] with B
      exact hAction B
    _ = ∑ e : Link,
          ∫ B : Cfg, E ((A e)⁻¹ * B e)
            ∂(Measure.pi (fun _ : Link => nu)) := by
      simpa using
        (MeasureTheory.integral_finset_sum
          (μ := Measure.pi (fun _ : Link => nu))
          (s := (Finset.univ : Finset Link))
          (f := fun (e : Link) (B : Cfg) => E ((A e)⁻¹ * B e))
          (by intro e _; exact hPiIntegrable e))
    _ = ∑ e : Link,
          ∫ b : G, E ((A e)⁻¹ * b) ∂nu := by
      apply Finset.sum_congr rfl
      intro e _
      exact hCoordinateIntegral e
    _ = ∑ _e : Link, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      exact p4Q2PZ37ANV_originalRelativeLinkEnergy_haarMean_one (A e)
    _ = (Fintype.card Link : ℝ) := by simp

/-- Exact symmetry of the unchanged true temporal Wilson crossing ACTION,
not just symmetry of its exponential Boltzmann kernel. -/
theorem p4Q2PZ37ANV_originalCrossingAction_symmetric
    (H : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 B A := by
  classical
  simp only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction,
    periodicHypercubicEvenSpatialSliceLinkList, Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro e _
  have h :=
    specialUnitaryWilsonPlaquetteEnergy_inv ((A e)⁻¹ * B e)
  simpa only [mul_inv_rev, inv_inv] using h.symm

/-- Consequently the exact original crossing action, averaged over its
LEFT Haar boundary, is constant in the true RIGHT boundary. This is
the direction required in the ANU first-action Haar moment. -/
theorem p4Q2PZ37ANV_originalCrossingAction_leftHaarMean
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) := by
  calc
    _ = ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 B A
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact p4Q2PZ37ANV_originalCrossingAction_symmetric H A B
    _ = _ := p4Q2PZ37ANV_originalCrossingAction_rightHaarMean H B


/-- SU(2)'s original negative identity is central.  This is proved from
the literal 2x2 complex matrices, rather than postulated as a lattice
independence axiom. -/
theorem p4Q2PZ37ANV_negativeIdentity_commutes (g : G) :
    g * specialUnitaryTwoNegativeIdentity =
      specialUnitaryTwoNegativeIdentity * g := by
  apply Subtype.ext
  change
    ((g : G) : Matrix (Fin 2) (Fin 2) ℂ) *
        (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (-(1 : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((g : G) : Matrix (Fin 2) (Fin 2) ℂ)
  simp

/-- The actual SU(2) fundamental Wilson character is exactly odd under
multiplication by the real negative-identity central element.
This is the sign-change needed for the genuine product-Haar
cross-plaquette cancellation and does not assume plaquette independence. -/
theorem p4Q2PZ37ANV_originalCharacter_centerFlip (g : G) :
    Chi (g * specialUnitaryTwoNegativeIdentity) = -Chi g := by
  dsimp [p4Q2PZ35C_originalOneLinkCharacter]
  rw [specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  ring


/-- Exact *real Hilbert* degree-one Gram-Schmidt normalization. The
signed coefficient is fixed by the original order (degree-zero constant,
then degree-one Wilson energy), never chosen after the fact. -/
private theorem p4Q2PZ37ANV_gramSchmidt_first_signedCentered
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E)
    (hUnit : ‖f 0‖ = 1)
    (hMean : inner ℝ (f 0) (f 1) = 1)
    (hCenteredNorm : ‖f 1 - f 0‖ = (1 / 2 : ℝ)) :
    InnerProductSpace.gramSchmidtNormed ℝ f 1 =
      (2 : ℝ) • (f 1 - f 0) := by
  have hIio : Finset.Iio (1 : ℕ) = {0} := by
    ext i
    simp only [Finset.mem_Iio, Finset.mem_singleton]
    omega
  have hZero : InnerProductSpace.gramSchmidt ℝ f 0 = f 0 := by
    simpa using (InnerProductSpace.gramSchmidt_bot (𝕜 := ℝ) f)
  have hTri := InnerProductSpace.gramSchmidt_def'' ℝ f 1
  rw [hIio] at hTri
  simp only [Finset.sum_singleton] at hTri
  rw [hZero, hMean, hUnit] at hTri
  have hTri' :
      f 1 = InnerProductSpace.gramSchmidt ℝ f 1 + f 0 := by
    -- The scalar coefficient contains a coercion of the real norm.
    simpa using hTri
  have hGS :
      InnerProductSpace.gramSchmidt ℝ f 1 = f 1 - f 0 := by
    calc
      _ = (InnerProductSpace.gramSchmidt ℝ f 1 + f 0) - f 0 := by abel
      _ = f 1 - f 0 := by rw [← hTri']
  unfold InnerProductSpace.gramSchmidtNormed
  rw [hGS, hCenteredNorm]
  norm_num

/-- ORIGINAL SU(2) Wilson-energy first Gram-Schmidt mode: exact positive
normalization of the centered degree-one ORIGINAL Haar L² energy. This
uses original character variance 1/4 and proves the sign from mathlib's
real Gram-Schmidt algorithm rather than assuming an arbitrary orientation. -/
theorem p4Q2PZ37ANV_originalWilsonGramSchmidtFirst_signedCentered :
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1 =
      (2 : ℝ) •
        (specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
            (by norm_num : 0 < (2 : ℕ)) 1 -
          Lp.const 2 nu (1 : ℝ)) := by
  let f : ℕ → SpecialUnitaryNormalizedHaarL2 2 :=
    fun k => specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
      (by norm_num : 0 < (2 : ℕ)) k
  have hZero :
      f 0 = Lp.const 2 nu (1 : ℝ) :=
    p4Q2PZ37ANI_originalWilsonEnergyPowerZero_eq_constOne
  have hOneNorm : ‖Lp.const 2 nu (1 : ℝ)‖ = 1 := by
    simpa [measureReal_def] using
      (Lp.norm_const (μ := nu) (p := 2) (c := (1 : ℝ)) (by norm_num))
  have hUnit : ‖f 0‖ = 1 := by
    rw [hZero]
    exact hOneNorm
  have hPowerRep :=
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_coeFn
      (by norm_num : 0 < (2 : ℕ)) 1
  have hPowerOne (g : G) :
      specialUnitaryWilsonPlaquetteEnergyPower 2 1 g =
        specialUnitaryWilsonPlaquetteEnergy 2 g := by
    simp only [specialUnitaryWilsonPlaquetteEnergyPower, pow_one]
  have hRepOne :
      f 1 =ᵐ[nu] (fun g : G => specialUnitaryWilsonPlaquetteEnergy 2 g) := by
    -- Transport the original MemLp representative lemma first; simplify
    -- the scalar power pointwise instead of expanding the L² vector.
    exact hPowerRep.trans (Filter.Eventually.of_forall hPowerOne)
  have hRepZero : f 0 =ᵐ[nu] (fun _ : G => (1 : ℝ)) := by
    rw [hZero]
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (μ := nu) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))
  have hRepCentered :
      (f 1 - f 0) =ᵐ[nu] (fun g : G => -Chi g) := by
    filter_upwards [Lp.coeFn_sub (f 1) (f 0), hRepOne, hRepZero]
      with g hsub he hzero
    calc
      (f 1 - f 0) g = f 1 g - f 0 g := by
        simpa only [Pi.sub_apply] using hsub
      _ = -Chi g := by
        rw [he, hzero]
        dsimp [p4Q2PZ35C_originalOneLinkCharacter]
        ring
  have hMean : inner ℝ (f 0) (f 1) = 1 := by
    calc
      _ = ∫ g : G, f 1 g ∂nu := by
        rw [hZero]
        exact realL2_inner_const_one_eq_integral (f 1)
      _ = ∫ g : G, specialUnitaryWilsonPlaquetteEnergy 2 g ∂nu :=
        integral_congr_ae hRepOne
      _ = 1 := by
        have h := p4Q2PZ37ANV_originalRelativeLinkEnergy_haarMean_one (1 : G)
        simpa only [inv_one, one_mul] using h
  have hCenteredSquare : ‖f 1 - f 0‖ ^ 2 = (1 / 4 : ℝ) := by
    calc
      _ = ∫ g : G, ‖(f 1 - f 0) g‖ ^ 2 ∂nu :=
        realL2_norm_sq_eq_integral_norm_sq (f 1 - f 0)
      _ = ∫ g : G, (Chi g) ^ 2 ∂nu := by
        apply integral_congr_ae
        filter_upwards [hRepCentered] with g hg
        rw [hg]
        simp [Real.norm_eq_abs, sq_abs]
      _ = (1 / 4 : ℝ) :=
        GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment
  have hCenteredNorm : ‖f 1 - f 0‖ = (1 / 2 : ℝ) := by
    have hNonneg := norm_nonneg (f 1 - f 0)
    nlinarith
  change InnerProductSpace.gramSchmidtNormed ℝ f 1 =
      (2 : ℝ) • (f 1 - Lp.const 2 nu (1 : ℝ))
  rw [← hZero]
  exact p4Q2PZ37ANV_gramSchmidt_first_signedCentered
    f hUnit hMean hCenteredNorm


/-! ## ANV: genuine spatial plaquette incidence, first geometric bridge

These results work on the existing oriented positive-link carrier, never on
a quotient by unoriented edges. The all-plaquette two-link uniqueness theorem
is valid at periodic side length >= 3; the length-2 case must be separately
checked rather than silently included.
-/

/-- The first origin link of the actual canonical spatial plaquette belongs to
its intrinsic four-link support. -/
theorem p4Q2PZ37ANV_primaryOriginOne_mem_support (H : ℕ) :
    p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∈
      pz37zaSpatialPlaquetteSupport H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) := by
  classical
  change p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∈
    (Finset.univ : Finset (Fin 4)).image
      (pz37zaSpatialPlaquetteBoundary H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

/-- The other origin link (direction 2) also belongs to the actual primary
plaquette's support. It is a different positive link from direction 1. -/
theorem p4Q2PZ37ANV_primaryOriginTwo_mem_support (H : ℕ) :
    p4Q2PZ37AMS_primarySpatialSliceEdge H 3 ∈
      pz37zaSpatialPlaquetteSupport H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) := by
  classical
  change p4Q2PZ37AMS_primarySpatialSliceEdge H 3 ∈
    (Finset.univ : Finset (Fin 4)).image
      (pz37zaSpatialPlaquetteBoundary H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩

/-- For every even periodic spatial side length at least four, two actual
positive origin links in distinct directions force a spatial plaquette to be
the canonical primary plaquette. Uses the previously proved exact physical
incidence uniqueness, NOT a new plaquette-independence premise.

The genuine side-length-two boundary H=0 is intentionally not included:
the general physical two-link uniqueness lemma requires side length >= 3. -/
theorem p4Q2PZ37ANV_primaryOriginTwoLinks_unique_of_H_pos
    (H : ℕ) (hH : 1 ≤ H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hOne : p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∈
      pz37zaSpatialPlaquetteSupport H p)
    (hTwo : p4Q2PZ37AMS_primarySpatialSliceEdge H 3 ∈
      pz37zaSpatialPlaquetteSupport H p) :
    p = p4Q2PZ37AMS_primarySpatialSlicePlaquette H := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    change 2 * (H + 1) ≠ 0
    omega⟩
  let p0 := p4Q2PZ37AMS_primarySpatialSlicePlaquette H
  let e1 := p4Q2PZ37AMS_primarySpatialSliceEdge H 0
  let e2 := p4Q2PZ37AMS_primarySpatialSliceEdge H 3
  have hlen : 3 ≤ PeriodicHypercubicEvenSideLength H := by
    change 3 ≤ 2 * (H + 1)
    omega
  have hdiff : e2 ≠ e1 := by
    intro h
    have hi : (3 : Fin 4) = 0 :=
      (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H).injective h
    exact (by decide : (3 : Fin 4) ≠ 0) hi
  have hfullDiff :
      periodicHypercubicEvenSpatialSliceLinkEmbedding H e2 ≠
        periodicHypercubicEvenSpatialSliceLinkEmbedding H e1 := by
    intro h
    exact hdiff
      (periodicHypercubicEvenSpatialSliceLinkEmbedding_injective H h)
  have hp1 : periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p e1 :=
    pz37zaSpatialPlaquetteSupport_mem_touches H p e1 hOne
  have hp2 : periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p e2 :=
    pz37zaSpatialPlaquetteSupport_mem_touches H p e2 hTwo
  have hp01 : periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p0 e1 :=
    pz37zaSpatialPlaquetteSupport_mem_touches H p0 e1
      (p4Q2PZ37ANV_primaryOriginOne_mem_support H)
  have hp02 : periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p0 e2 :=
    pz37zaSpatialPlaquetteSupport_mem_touches H p0 e2
      (p4Q2PZ37ANV_primaryOriginTwo_mem_support H)
  apply periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_injective H
  exact periodicHypercubicPlaquette_eq_of_touches_two_edges
    (PeriodicHypercubicEvenSideLength H) hlen
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H e1)
    (periodicHypercubicEvenSpatialSliceLinkEmbedding H e2) hfullDiff
    (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p)
    (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p0)
    hp1 hp2 hp01 hp02

/-- Construct a link in the genuine primary plaquette absent from any
different spatial plaquette at periodic side length >= 4. -/
theorem p4Q2PZ37ANV_primaryHasExclusiveLink_of_H_pos
    (H : ℕ) (hH : 1 ≤ H)
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hp : p ≠ p4Q2PZ37AMS_primarySpatialSlicePlaquette H) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      e ∈ pz37zaSpatialPlaquetteSupport H
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) ∧
      e ∉ pz37zaSpatialPlaquetteSupport H p := by
  by_cases he : p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∈
      pz37zaSpatialPlaquetteSupport H p
  · refine ⟨p4Q2PZ37AMS_primarySpatialSliceEdge H 3,
      p4Q2PZ37ANV_primaryOriginTwo_mem_support H, ?_⟩
    intro he2
    exact hp
      (p4Q2PZ37ANV_primaryOriginTwoLinks_unique_of_H_pos
        H hH p he he2)
  · exact ⟨p4Q2PZ37AMS_primarySpatialSliceEdge H 0,
      p4Q2PZ37ANV_primaryOriginOne_mem_support H, he⟩


/-! ## ANV: length-two exceptional geometry and all-H incidence

H = 0 is the genuine spatial torus of periodic side length 2. The global
shared-two-edge uniqueness theorem requires side length >= 3, so this leaf
checks the *particular perpendicular origin links* in the unchanged
time-zero spatial carrier. No n >= 3 hypothesis is silently dropped.
-/

/-- The exceptional genuine even torus H=0: of the 24 time-zero
coordinate plaquettes, only the canonical (1,2)-plaquette can contain
both distinct positive links at the origin in directions 1 and 2.
The exact finite carrier is enumerated, not replaced by a proxy. -/
theorem p4Q2PZ37ANV_primaryOriginTwoLinks_unique_of_H_zero
    (p : PeriodicHypercubicEvenSpatialSlicePlaquette 0)
    (hOne : p4Q2PZ37AMS_primarySpatialSliceEdge 0 0 ∈
      pz37zaSpatialPlaquetteSupport 0 p)
    (hTwo : p4Q2PZ37AMS_primarySpatialSliceEdge 0 3 ∈
      pz37zaSpatialPlaquetteSupport 0 p) :
    p = p4Q2PZ37AMS_primarySpatialSlicePlaquette 0 := by
  classical
  have hOne' :
      ∃ i : Fin 4,
        pz37zaSpatialPlaquetteBoundary 0 p i =
          p4Q2PZ37AMS_primarySpatialSliceEdge 0 0 := by
    change p4Q2PZ37AMS_primarySpatialSliceEdge 0 0 ∈
      (Finset.univ : Finset (Fin 4)).image
        (pz37zaSpatialPlaquetteBoundary 0 p) at hOne
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hOne
    exact ⟨i, hi⟩
  have hTwo' :
      ∃ j : Fin 4,
        pz37zaSpatialPlaquetteBoundary 0 p j =
          p4Q2PZ37AMS_primarySpatialSliceEdge 0 3 := by
    change p4Q2PZ37AMS_primarySpatialSliceEdge 0 3 ∈
      (Finset.univ : Finset (Fin 4)).image
        (pz37zaSpatialPlaquetteBoundary 0 p) at hTwo
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hTwo
    exact ⟨j, hj⟩
  let p0 := p4Q2PZ37AMS_primarySpatialSlicePlaquette 0
  have he1Dir :
      (p4Q2PZ37AMS_primarySpatialSliceEdge 0 0).2.1 =
        (1 : PeriodicHypercubicAxis) := by rfl
  have he2Dir :
      (p4Q2PZ37AMS_primarySpatialSliceEdge 0 3).2.1 =
        (2 : PeriodicHypercubicAxis) := by rfl
  have he1Source :
      (p4Q2PZ37AMS_primarySpatialSliceEdge 0 0).1 = p0.1 := by rfl
  have he2Source :
      (p4Q2PZ37AMS_primarySpatialSliceEdge 0 3).1 = p0.1 := by rfl
  -- First read both directions of the actual four-link boundary. The
  -- finite case split is on Fin 4, NOT on the dependent plaquette Fintype:
  -- fin_cases on the latter failed to eliminate Fintype.elems/Eq.rec.
  have hBoundaryDir (i : Fin 4) :
      (pz37zaSpatialPlaquetteBoundary 0 p i).2.1 = p.2.1.1.1 ∨
      (pz37zaSpatialPlaquetteBoundary 0 p i).2.1 = p.2.1.2.1 := by
    fin_cases i <;> simp [pz37zaSpatialPlaquetteBoundary]
  have hHasDir1 :
      p.2.1.1.1 = (1 : PeriodicHypercubicAxis) ∨
      p.2.1.2.1 = (1 : PeriodicHypercubicAxis) := by
    obtain ⟨i, hi⟩ := hOne'
    have hDir := (congrArg
      (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.2.1) hi).trans he1Dir
    rcases hBoundaryDir i with h | h
    · exact Or.inl (h.symm.trans hDir)
    · exact Or.inr (h.symm.trans hDir)
  have hHasDir2 :
      p.2.1.1.1 = (2 : PeriodicHypercubicAxis) ∨
      p.2.1.2.1 = (2 : PeriodicHypercubicAxis) := by
    obtain ⟨j, hj⟩ := hTwo'
    have hDir := (congrArg
      (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.2.1) hj).trans he2Dir
    rcases hBoundaryDir j with h | h
    · exact Or.inl (h.symm.trans hDir)
    · exact Or.inr (h.symm.trans hDir)
  have hAxisOrder : p.2.1.1.1 < p.2.1.2.1 := p.2.2
  -- The axis type is Fin 4.  Use literal finite-order contradictions:
  -- omega cannot extract arithmetic constraints from the nested subtype
  -- projections of the original dependent spatial plaquette here.
  have hDirections :
      p.2.1.1.1 = (1 : PeriodicHypercubicAxis) ∧
        p.2.1.2.1 = (2 : PeriodicHypercubicAxis) := by
    rcases hHasDir1 with h1 | h1
    · rcases hHasDir2 with h2 | h2
      · exact False.elim ((by decide : (1 : PeriodicHypercubicAxis) ≠ 2)
          (h1.symm.trans h2))
      · exact ⟨h1, h2⟩
    · rcases hHasDir2 with h2 | h2
      · have hBad : (2 : PeriodicHypercubicAxis) <
            (1 : PeriodicHypercubicAxis) := by
          simpa only [h2, h1] using hAxisOrder
        exact False.elim ((by decide :
          ¬ ((2 : PeriodicHypercubicAxis) < (1 : PeriodicHypercubicAxis))) hBad)
      · exact False.elim ((by decide : (1 : PeriodicHypercubicAxis) ≠ 2)
          (h1.symm.trans h2))
  have hFirstDir : p.2.1.1.1 = (1 : PeriodicHypercubicAxis) :=
    hDirections.1
  have hSecondDir : p.2.1.2.1 = (2 : PeriodicHypercubicAxis) :=
    hDirections.2
  have hPair : p.2 = p0.2 := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact hFirstDir
    · apply Subtype.ext
      exact hSecondDir
  -- Among the four original link positions, the first origin direction
  -- can only occur at the base or at the transverse shifted base.
  have hOneBase :
      p.1 = p0.1 ∨
        periodicHypercubicEvenSpatialSliceShift 0 p.1 p.2.1.2 = p0.1 := by
    obtain ⟨i, hi⟩ := hOne'
    fin_cases i
    · left
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.1) hi).trans he1Source
      simpa [pz37zaSpatialPlaquetteBoundary] using h
    · exfalso
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.2.1) hi).trans he1Dir
      have hbad : p.2.1.2.1 = (1 : PeriodicHypercubicAxis) := by
        simpa [pz37zaSpatialPlaquetteBoundary] using h
      exact (by decide : (2 : PeriodicHypercubicAxis) ≠ 1)
        (hSecondDir.symm.trans hbad)
    · right
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.1) hi).trans he1Source
      simpa [pz37zaSpatialPlaquetteBoundary] using h
    · exfalso
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.2.1) hi).trans he1Dir
      have hbad : p.2.1.2.1 = (1 : PeriodicHypercubicAxis) := by
        simpa [pz37zaSpatialPlaquetteBoundary] using h
      exact (by decide : (2 : PeriodicHypercubicAxis) ≠ 1)
        (hSecondDir.symm.trans hbad)
  have hTwoBase :
      periodicHypercubicEvenSpatialSliceShift 0 p.1 p.2.1.1 = p0.1 ∨
        p.1 = p0.1 := by
    obtain ⟨j, hj⟩ := hTwo'
    fin_cases j
    · exfalso
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.2.1) hj).trans he2Dir
      have hbad : p.2.1.1.1 = (2 : PeriodicHypercubicAxis) := by
        simpa [pz37zaSpatialPlaquetteBoundary] using h
      exact (by decide : (1 : PeriodicHypercubicAxis) ≠ 2)
        (hFirstDir.symm.trans hbad)
    · left
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.1) hj).trans he2Source
      simpa [pz37zaSpatialPlaquetteBoundary] using h
    · exfalso
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.2.1) hj).trans he2Dir
      have hbad : p.2.1.1.1 = (2 : PeriodicHypercubicAxis) := by
        simpa [pz37zaSpatialPlaquetteBoundary] using h
      exact (by decide : (1 : PeriodicHypercubicAxis) ≠ 2)
        (hFirstDir.symm.trans hbad)
    · right
      have h := (congrArg
        (fun e : PeriodicHypercubicEvenSpatialSliceLink 0 => e.1) hj).trans he2Source
      simpa [pz37zaSpatialPlaquetteBoundary] using h
  have hOrigin : p.1 = p0.1 := by
    rcases hOneBase with hbase | hshift2
    · exact hbase
    rcases hTwoBase with hshift1 | hbase
    · exfalso
      have hShiftEq :
          periodicHypercubicEvenSpatialSliceShift 0 p.1 p.2.1.2 =
            periodicHypercubicEvenSpatialSliceShift 0 p.1 p.2.1.1 :=
        hshift2.trans hshift1.symm
      have hFullShiftEq :
          periodicHypercubicShift 2 p.1.1 p.2.1.2.1 =
            periodicHypercubicShift 2 p.1.1 p.2.1.1.1 := by
        simpa only [periodicHypercubicEvenSpatialSliceShift_coe] using
          congrArg Subtype.val hShiftEq
      have hDirEq : p.2.1.2.1 = p.2.1.1.1 :=
        periodicHypercubicShift_axis_injective 2 (by norm_num) p.1.1 hFullShiftEq
      exact (ne_of_gt p.2.2) hDirEq
    · exact hbase
  exact Prod.ext hOrigin hPair

/-- Both specific canonical origin links determine the same genuine
spatial plaquette for *all* finite H, including the length-two torus. -/
theorem p4Q2PZ37ANV_primaryOriginTwoLinks_unique
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hOne : p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∈
      pz37zaSpatialPlaquetteSupport H p)
    (hTwo : p4Q2PZ37AMS_primarySpatialSliceEdge H 3 ∈
      pz37zaSpatialPlaquetteSupport H p) :
    p = p4Q2PZ37AMS_primarySpatialSlicePlaquette H := by
  cases H with
  | zero =>
      exact p4Q2PZ37ANV_primaryOriginTwoLinks_unique_of_H_zero p hOne hTwo
  | succ H =>
      exact p4Q2PZ37ANV_primaryOriginTwoLinks_unique_of_H_pos
        (H + 1) (by omega) p hOne hTwo

/-- For any H and a spatial plaquette different from the primary,
some actual primary positive link is absent from the other plaquette.
This is the specific incidence fact required for Wilson character
cross-Haar orthogonality under a single-link center flip. -/
theorem p4Q2PZ37ANV_primaryHasExclusiveLink
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hp : p ≠ p4Q2PZ37AMS_primarySpatialSlicePlaquette H) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      e ∈ pz37zaSpatialPlaquetteSupport H
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) ∧
      e ∉ pz37zaSpatialPlaquetteSupport H p := by
  by_cases he : p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∈
      pz37zaSpatialPlaquetteSupport H p
  · refine ⟨p4Q2PZ37AMS_primarySpatialSliceEdge H 3,
      p4Q2PZ37ANV_primaryOriginTwo_mem_support H, ?_⟩
    intro he2
    exact hp (p4Q2PZ37ANV_primaryOriginTwoLinks_unique H p he he2)
  · exact ⟨p4Q2PZ37AMS_primarySpatialSliceEdge H 0,
      p4Q2PZ37ANV_primaryOriginOne_mem_support H, he⟩


/-! ## ANV: cancellation in the genuine two-boundary Haar action

No plaquette-independence hypothesis is introduced.  The temporal crossing
term is integrated in its first physical boundary using the exact original
Haar law, and the actual primary spatial character is integrated in its
second boundary.  In particular this calculation also covers H = 0. -/

/-- The genuine ORIGINAL temporal crossing Wilson action is exactly
orthogonal to the genuine primary SU(2) Wilson character under iterated
two-boundary product Haar.  It uses the unchanged actual linkwise crossing
action, not a proxy single-link kernel. -/
theorem p4Q2PZ37ANV_originalCrossing_primaryCharacter_iteratedHaar_zero
    (H : ℕ) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
          H 2 A B *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  classical
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hInner (B : Cfg) :
      (∫ A : Cfg,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
          H 2 A B *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂muH) =
        (Fintype.card Link : ℝ) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) := by
    rw [integral_mul_const]
    rw [p4Q2PZ37ANV_originalCrossingAction_leftHaarMean H B]
  calc
    _ = ∫ B : Cfg,
          (Fintype.card Link : ℝ) *
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
          ∂muH := by
            apply integral_congr_ae
            filter_upwards [] with B
            exact hInner B
    _ = (Fintype.card Link : ℝ) *
          (∫ B : Cfg,
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
            ∂muH) := by rw [integral_const_mul]
    _ = 0 := by
      rw [p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero H]
      ring

/-- The ORIGINAL spatial action on the opposite Haar boundary contributes
no first-character insertion.  The full action remains unchanged; this is
one exact term of its symmetric one-slab decomposition. -/
theorem p4Q2PZ37ANV_originalLeftSpatialAction_primaryCharacter_iteratedHaar_zero
    (H : ℕ) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hInner (B : Cfg) :
      (∫ A : Cfg,
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂muH) =
        (∫ A : Cfg,
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A
          ∂muH) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) := by
    rw [integral_mul_const]
  calc
    _ = ∫ B : Cfg,
          (∫ A : Cfg,
            periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A
            ∂muH) *
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
          ∂muH := by
            apply integral_congr_ae
            filter_upwards [] with B
            exact hInner B
    _ = (∫ A : Cfg,
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A
          ∂muH) *
          (∫ B : Cfg,
            Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
            ∂muH) := by rw [integral_const_mul]
    _ = 0 := by
      rw [p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero H]
      ring


/-- The original *intrinsic* spatial-slice primary Wilson energy agrees
pointwise with its four-native-link cyclic Haar representative.
The agreement follows from the already proved native holonomy conjugacy
and Wilson class-function invariance; no plaquette substitution occurs. -/
theorem p4Q2PZ37ANV_originalPrimarySpatialEnergy_eq_cyclic
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)) =
      specialUnitaryWilsonPlaquetteEnergy 2
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) := by
  rw [p4Q2PZ37AMT_spatialHolonomy_eq_orientedFourEdge]
  simpa only [p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy] using
    (specialUnitaryWilsonPlaquetteEnergy_orientedFourEdge_eq_cyclic
      (fun k : Fin 4 =>
        A (p4Q2PZ37AMS_primarySpatialSliceEdgeEmbedding H k)))

/-- Exact *original native spatial plaquette* Haar energy-character
pairing. The value -1/4 belongs to the unchanged oriented Wilson
holonomy, transferred through a proved pointwise conjugacy to cyclic
Haar—not obtained by assuming independent plaquettes. -/
theorem p4Q2PZ37ANV_originalNativePrimarySpatialEnergyCharacter_haarPairing
    (H : ℕ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)) *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        -(1 / 4 : ℝ) := by
  calc
    _ = ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
          specialUnitaryWilsonPlaquetteEnergy 2
            (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
            apply integral_congr_ae
            filter_upwards [] with A
            rw [p4Q2PZ37ANV_originalPrimarySpatialEnergy_eq_cyclic H A]
    _ = -(1 / 4 : ℝ) :=
      p4Q2PZ37ANV_originalTimeZeroPrimaryEnergyCharacter_haarPairing H


/-! ## ANV: native one-link center twist, original product Haar -/

/-- Change exactly one original positive time-zero spatial link by the
genuine SU(2) central negative identity. -/
noncomputable def p4Q2PZ37ANV_singleLinkCenterTwist
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  fun e => A e * (if e = target then specialUnitaryTwoNegativeIdentity else 1)

/-- The single genuine native-link center twist preserves the unchanged
link-indexed product-Haar law, by original coordinate Haar invariance. -/
theorem p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    MeasurePreserving
      (p4Q2PZ37ANV_singleLinkCenterTwist H target)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  classical
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let f : Link → G → G :=
    fun e u => u * (if e = target then specialUnitaryTwoNegativeIdentity else 1)
  have hMP (e : Link) : MeasurePreserving (f e) nu nu := by
    simpa [f] using
      (normalizedCompactHaar_measurePreserving_mul_left_right G (1 : G)
        (if e = target then specialUnitaryTwoNegativeIdentity else 1))
  refine ⟨?_, ?_⟩
  · unfold p4Q2PZ37ANV_singleLinkCenterTwist
    refine measurable_pi_lambda _ ?_
    intro e
    exact (hMP e).measurable.comp (measurable_pi_apply e)
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    have hf : ∀ e : Link, AEMeasurable (f e) nu :=
      fun e => (hMP e).measurable.aemeasurable
    letI : ∀ e : Link, SigmaFinite (Measure.map (f e) nu) :=
      fun e => by
        rw [(hMP e).map_eq]
        infer_instance
    rw [show p4Q2PZ37ANV_singleLinkCenterTwist H target =
      (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact (hMP e).map_eq

/-- A genuine plaquette omitting the twisted positive link retains
its literal original oriented four-link SU(2) holonomy. -/
theorem p4Q2PZ37ANV_singleLinkCenterTwist_holonomy_of_not_mem
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hnot : target ∉ pz37zaSpatialPlaquetteSupport H p)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      (p4Q2PZ37ANV_singleLinkCenterTwist H target A) p =
      periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p := by
  classical
  have hnone (k : Fin 4) :
      pz37zaSpatialPlaquetteBoundary H p k ≠ target := by
    intro hk
    apply hnot
    change target ∈
      (Finset.univ : Finset (Fin 4)).image
        (pz37zaSpatialPlaquetteBoundary H p)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  have h0 : (p.1, p.2.1.1) ≠ target := by
    simpa [pz37zaSpatialPlaquetteBoundary] using hnone 0
  have h1 :
      (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1,
        p.2.1.2) ≠ target := by
    simpa [pz37zaSpatialPlaquetteBoundary] using hnone 1
  have h2 :
      (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2,
        p.2.1.1) ≠ target := by
    simpa [pz37zaSpatialPlaquetteBoundary] using hnone 2
  have h3 : (p.1, p.2.1.2) ≠ target := by
    simpa [pz37zaSpatialPlaquetteBoundary] using hnone 3
  simp [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
    p4Q2PZ37ANV_singleLinkCenterTwist, h0, h1, h2, h3]

/-- Therefore the unchanged original Wilson plaquette energy outside
the twisted link support is invariant pointwise, even at H = 0. -/
theorem p4Q2PZ37ANV_singleLinkCenterTwist_energy_of_not_mem
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hnot : target ∉ pz37zaSpatialPlaquetteSupport H p)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        (p4Q2PZ37ANV_singleLinkCenterTwist H target A) p) =
      specialUnitaryWilsonPlaquetteEnergy 2
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := by
  rw [p4Q2PZ37ANV_singleLinkCenterTwist_holonomy_of_not_mem
    H p target hnot A]


/-! ## ANV: four-edge SU(2) center oddness and off-diagonal Haar pairing

Reuse the independently certified PU actual one-link Haar center flip,
PU3 original four-link distinctness, and PV first-three-link oddness.
The fourth inverse-oriented edge is handled explicitly. Together with
the ANV all-H exclusive-link theorem, no assumption of independent
plaquettes or a changed physical Haar space is needed. -/

section NativePlaquetteCenterCancellation

local notation "e0" =>
  GroundStatePosteriorJoint.p4Q2PU3_originalPlaquetteEdge0
local notation "e1" =>
  GroundStatePosteriorJoint.p4Q2PU3_originalPlaquetteEdge1
local notation "e2" =>
  GroundStatePosteriorJoint.p4Q2PU3_originalPlaquetteEdge2
local notation "e3" =>
  GroundStatePosteriorJoint.p4Q2PU3_originalPlaquetteEdge3
local notation "Flip" =>
  GroundStatePosteriorJoint.p4Q2PU_originalSpatialSingleLinkCenterFlip
local notation "Hol" =>
  periodicHypercubicEvenSpatialSlicePlaquetteHolonomy

/-- The fourth original inverse-oriented spatial link also flips the
exact four-link Wilson holonomy by the same genuine SU(2) center.
The previously certified PV proof had handled the other three links. -/
theorem p4Q2PZ37ANV_originalPlaquetteHolonomy_flip_fourth
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Hol (Flip H (e3 H p) A) p =
      Hol A p * specialUnitaryTwoNegativeIdentity := by
  obtain ⟨h30, h31, h32⟩ :=
    GroundStatePosteriorJoint.p4Q2PU3_originalPlaquette_last_distinct H p
  change
    (Flip H (e3 H p) A (e0 H p)) *
      (Flip H (e3 H p) A (e1 H p)) *
      (Flip H (e3 H p) A (e2 H p))⁻¹ *
      (Flip H (e3 H p) A (e3 H p))⁻¹ =
    (A (e0 H p) * A (e1 H p) *
      (A (e2 H p))⁻¹ * (A (e3 H p))⁻¹) *
        specialUnitaryTwoNegativeIdentity
  rw [GroundStatePosteriorJoint.p4Q2PU_originalSingleLinkCenterFlip_other
        H (e3 H p) (e0 H p) h30.symm A,
      GroundStatePosteriorJoint.p4Q2PU_originalSingleLinkCenterFlip_other
        H (e3 H p) (e1 H p) h31.symm A,
      GroundStatePosteriorJoint.p4Q2PU_originalSingleLinkCenterFlip_other
        H (e3 H p) (e2 H p) h32.symm A,
      GroundStatePosteriorJoint.p4Q2PU_originalSingleLinkCenterFlip_at
        H (e3 H p) A]
  rw [GroundStatePosteriorJoint.p4Q2PV_originalSU2Center_inverse_mul
    (A (e3 H p))]
  exact (mul_assoc _ _ _).symm

/-- The literal original spatial Wilson real character is odd even
under the previously missing fourth inverse-oriented link flip. -/
theorem p4Q2PZ37ANV_originalPlaquetteCharacter_flip_fourth
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H p
        (Flip H (e3 H p) A) =
      -GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H p A := by
  unfold GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter
  rw [p4Q2PZ37ANV_originalPlaquetteHolonomy_flip_fourth H p A,
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  ring

/-- Identical first SU(2) character in the native original oriented
plaquette and the AMT-certified cyclic four-Haar representative. -/
theorem p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) =
      GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) A := by
  dsimp [p4Q2PZ35C_originalOneLinkCharacter,
    GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter]
  rw [p4Q2PZ37ANV_originalPrimarySpatialEnergy_eq_cyclic H A]

/-- For either of two exclusive primary origin links, the real Wilson
character changes sign under the unchanged original PU center flip.
H=0 is included by the genuinely native spatial-slice link types. -/
theorem p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hTarget : target = p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∨
      target = p4Q2PZ37AMS_primarySpatialSliceEdge H 3)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
      (Flip H target A)) =
      -Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) := by
  let p0 := p4Q2PZ37AMS_primarySpatialSlicePlaquette H
  calc
    _ = GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H p0
          (Flip H target A) :=
      p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H _
    _ = -GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H p0 A := by
      rcases hTarget with h0 | h3
      · subst target
        exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_centerOdd
          H p0 (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
          (Or.inl (by rfl)) A
      · subst target
        have he3 : p4Q2PZ37AMS_primarySpatialSliceEdge H 3 = e3 H p0 := by
          rfl
        simpa only [he3] using
          (p4Q2PZ37ANV_originalPlaquetteCharacter_flip_fourth H p0 A)
    _ = _ := by
      rw [p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H A]

/-- The new ANV coordinate twist equals the already certified PU
center flip on each genuine SU(2) spatial link, pointwise. -/
theorem p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU
    (H : ℕ) (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2PZ37ANV_singleLinkCenterTwist H target A =
      Flip H target A := by
  classical
  funext e
  by_cases he : e = target
  · simp [p4Q2PZ37ANV_singleLinkCenterTwist,
      GroundStatePosteriorJoint.p4Q2PU_originalSpatialSingleLinkCenterFlip, he]
  · simp [p4Q2PZ37ANV_singleLinkCenterTwist,
      GroundStatePosteriorJoint.p4Q2PU_originalSpatialSingleLinkCenterFlip, he]

/-- Under the ORIGINAL native spatial product Haar, any spatial
plaquette other than the physical primary is orthogonal to its
normalized SU(2) fundamental character, even on the H=0 period-two
torus. No artificial independent-plaquette measure is introduced. -/
theorem p4Q2PZ37ANV_nonPrimarySpatialEnergy_primaryCharacter_haarOrthogonal
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H)
    (hp : p ≠ p4Q2PZ37AMS_primarySpatialSlicePlaquette H) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      specialUnitaryWilsonPlaquetteEnergy 2
        (Hol A p) *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = 0 := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let p0 := p4Q2PZ37AMS_primarySpatialSlicePlaquette H
  obtain ⟨target, hChoice, hNot⟩ :
      ∃ target : Link,
        (target = p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∨
         target = p4Q2PZ37AMS_primarySpatialSliceEdge H 3) ∧
        target ∉ pz37zaSpatialPlaquetteSupport H p := by
    by_cases h0 : p4Q2PZ37AMS_primarySpatialSliceEdge H 0 ∈
        pz37zaSpatialPlaquetteSupport H p
    · refine ⟨p4Q2PZ37AMS_primarySpatialSliceEdge H 3, Or.inr rfl, ?_⟩
      intro h3
      exact hp (p4Q2PZ37ANV_primaryOriginTwoLinks_unique H p h0 h3)
    · exact ⟨p4Q2PZ37AMS_primarySpatialSliceEdge H 0, Or.inl rfl, h0⟩
  have hHolCont : Continuous (fun A : Cfg => Hol A p) := by
    unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
    fun_prop
  have hCharacterCont :
      Continuous (fun A : Cfg =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
    have hFun :
        (fun A : Cfg =>
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) =
        (fun A : Cfg =>
          GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H p0 A) := by
      funext A
      exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H A
    rw [hFun]
    exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous H p0
  have hCont : Continuous
      (fun A : Cfg =>
        specialUnitaryWilsonPlaquetteEnergy 2 (Hol A p) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) :=
    ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hHolCont).mul hCharacterCont
  have hEnergyFlip (A : Cfg) :
      specialUnitaryWilsonPlaquetteEnergy 2 (Hol (Flip H target A) p) =
        specialUnitaryWilsonPlaquetteEnergy 2 (Hol A p) := by
    rw [← p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU H target A]
    exact p4Q2PZ37ANV_singleLinkCenterTwist_energy_of_not_mem H p target hNot A
  have hOdd (A : Cfg) :
      specialUnitaryWilsonPlaquetteEnergy 2 (Hol (Flip H target A) p) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 (Flip H target A)) =
      -(specialUnitaryWilsonPlaquetteEnergy 2 (Hol A p) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
    rw [hEnergyFlip A,
      p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd H target hChoice A]
    ring
  exact GroundStatePosteriorJoint.p4Q2PU_originalCenterFlip_Haar_odd_integral_zero
    H target
    (fun A : Cfg =>
      specialUnitaryWilsonPlaquetteEnergy 2 (Hol A p) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A))
    hCont hOdd

end NativePlaquetteCenterCancellation


/-! ## ANV: native complete spatial Wilson action first Haar pairing -/

/-- The ORIGINAL, ALL-PLAQUETTE spatial Wilson action has the exact
first-character Haar pairing -1/4 at every genuine even-periodic H.
This uses the full actual spatial-plaquette finite-universe sum; all
nonprimary plaquettes are individually annihilated by the proven
one-link center-flip symmetry. Neither independent plaquettes nor
a synthetic single-character action are assumed. -/
theorem p4Q2PZ37ANV_originalFullSpatialAction_primaryCharacter_haarPairing
    (H : ℕ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      -(1 / 4 : ℝ) := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let p0 := p4Q2PZ37AMS_primarySpatialSlicePlaquette H
  let F : Plaq → Cfg → ℝ := fun p A =>
    specialUnitaryWilsonPlaquetteEnergy 2
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) *
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)
  have hCharacterCont :
      Continuous (fun A : Cfg =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
    have hFun :
        (fun A : Cfg =>
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) =
        (fun A : Cfg =>
          GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H p0 A) := by
      funext A
      exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H A
    rw [hFun]
    exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous H p0
  have hIntegrable (p : Plaq) : Integrable (F p) muH := by
    have hHolCont : Continuous
        (fun A : Cfg => periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p) := by
      unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
      fun_prop
    have hFCont : Continuous (F p) :=
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp hHolCont).mul
        hCharacterCont
    exact hFCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSum :
      (∑ p : Plaq, ∫ A : Cfg, F p A ∂muH) =
        ∫ A : Cfg, F p0 A ∂muH := by
    apply Finset.sum_eq_single p0
    · intro p _hp hpNe
      simpa only [F, muH, p0] using
        (p4Q2PZ37ANV_nonPrimarySpatialEnergy_primaryCharacter_haarOrthogonal
          H p hpNe)
    · intro hpAbsent
      exact False.elim (hpAbsent (Finset.mem_univ p0))
  calc
    (∫ A : Cfg,
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A) ∂muH) =
      ∫ A : Cfg, ∑ p : Plaq, F p A ∂muH := by
        apply integral_congr_ae
        filter_upwards [] with A
        rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum
          H 2 A, Finset.sum_mul]
        -- Two canonical Fintype instances enumerate the same physical
        -- plaquette type. Equality is extensional, not definitional.
        apply Finset.sum_congr
        · ext p
          simp
        · intro p _
          rfl
    _ = ∑ p : Plaq, ∫ A : Cfg, F p A ∂muH := by
        simpa using
          (MeasureTheory.integral_finset_sum
            (μ := muH)
            (s := (Finset.univ : Finset Plaq))
            (f := fun (p : Plaq) (A : Cfg) => F p A)
            (by intro p _; exact hIntegrable p))
    _ = ∫ A : Cfg, F p0 A ∂muH := hSum
    _ = -(1 / 4 : ℝ) := by
      simpa only [F, p0, muH] using
        (p4Q2PZ37ANV_originalNativePrimarySpatialEnergyCharacter_haarPairing H)


/-! ## ANV: authentic first Gauss-law mode as an exact signed Haar representative

The original ANU coefficient uses actual typed physical Hilbert vectors,
not a substitute observable. These lemmas make the exact almost-everywhere
representatives available to the unchanged pair-Haar L² tensor calculation.
They do not assert any OS-Wilson identification or continuum mass gap. -/

/-- The mathlib Gram-Schmidt first-degree Haar vector equals -2 times
the original normalized SU(2) fundamental Wilson character almost
everywhere, with the sign determined by original energy-power order. -/
theorem p4Q2PZ37ANV_originalFirstGramSchmidt_haarRepresentative :
    specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1 =ᵐ[nu]
      (fun g : G => (-2 : ℝ) * Chi g) := by
  let f1 : SpecialUnitaryNormalizedHaarL2 2 :=
    specialUnitaryWilsonPlaquetteEnergyPowerHaarL2
      (by norm_num : 0 < (2 : ℕ)) 1
  let f0 : SpecialUnitaryNormalizedHaarL2 2 :=
    Lp.const 2 nu (1 : ℝ)
  have hMode :
      specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1 =
        (2 : ℝ) • (f1 - f0) := by
    simpa only [f1, f0] using
      p4Q2PZ37ANV_originalWilsonGramSchmidtFirst_signedCentered
  have hPower : f1 =ᵐ[nu]
      (fun g : G => specialUnitaryWilsonPlaquetteEnergy 2 g) := by
    have h := specialUnitaryWilsonPlaquetteEnergyPowerHaarL2_coeFn
      (by norm_num : 0 < (2 : ℕ)) 1
    exact h.trans (Filter.Eventually.of_forall (fun g : G => by
      simp only [specialUnitaryWilsonPlaquetteEnergyPower, pow_one]))
  have hConst : f0 =ᵐ[nu] (fun _ : G => (1 : ℝ)) := by
    simpa only [f0, Function.const_apply] using
      (Lp.coeFn_const (μ := nu) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))
  rw [hMode]
  filter_upwards
    [Lp.coeFn_smul (2 : ℝ) (f1 - f0),
      Lp.coeFn_sub f1 f0, hPower, hConst]
    with g hsmul hsub hp hc
  calc
    ((2 : ℝ) • (f1 - f0)) g =
        (2 : ℝ) • ((f1 - f0) g) := hsmul
    _ = (-2 : ℝ) * Chi g := by
      rw [hsub, Pi.sub_apply, hp, hc]
      simp only [smul_eq_mul]
      dsimp [p4Q2PZ35C_originalOneLinkCharacter]
      ring

/-- The genuinely typed PHYSICAL Gauss-law first Wilson mode has the
unmodified cyclic primary-plaquette first-character representative.
The measure-preserving transport is AMS; physical typing is AMU. -/
theorem p4Q2PZ37ANV_actualPhysicalFirstGaussMode_haarRepresentative
    (H : ℕ) :
    ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2]
        (fun A => (-2 : ℝ) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) := by
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let phi := p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
  let v := specialUnitaryWilsonPlaquetteEnergyTwoHaarGramSchmidtMode 1
  have hMP : MeasurePreserving phi muH nu :=
    p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2
  have hSource : v =ᵐ[nu] (fun g : G => (-2 : ℝ) * Chi g) :=
    p4Q2PZ37ANV_originalFirstGramSchmidt_haarRepresentative
  have hComp :
      (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2) v
        =ᵐ[muH] v ∘ phi :=
    Lp.coeFn_compMeasurePreserving v hMP
  have hPulled :
      v ∘ phi =ᵐ[muH]
        (fun A => (-2 : ℝ) * Chi (phi A)) := by
    simpa only [Function.comp_def] using
      hMP.quasiMeasurePreserving.ae_eq hSource
  change
    (p4Q2PZ37AMS_primarySpatialSliceHolonomyL2Pullback H 2) v
      =ᵐ[muH] (fun A => (-2 : ℝ) * Chi (phi A))
  exact hComp.trans hPulled

/-- The genuine original physical Gauss-law constant unit vector is
pointwise represented by 1 almost everywhere in the native Haar L². -/
theorem p4Q2PZ37ANV_actualPhysicalConstant_haarRepresentative
    (H : ℕ) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2]
        (fun _ => (1 : ℝ)) := by
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  change Lp.const 2 muH (1 : ℝ) =ᵐ[muH] (fun _ => (1 : ℝ))
  simpa only [Function.const_apply] using
    (Lp.coeFn_const (μ := muH) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))


/-- The exact tensor appearing in ANU's **original physical** first
Haar-action moment has representative -2 times the actual canonical
spatial plaquette character in the second genuine Haar boundary.
This keeps Gauss-law source types and pair product Haar unchanged. -/
theorem p4Q2PZ37ANV_actualFirstPhysicalTensor_pairHaarRepresentative
    (H : ℕ) :
    (realL2ExternalTensor
      ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))
      =ᵐ[periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2]
        (fun p => (-2 : ℝ) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let f : Lp ℝ 2 muH :=
    ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
        Lp ℝ 2 muH)
  let g : Lp ℝ 2 muH :=
    ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
        Lp ℝ 2 muH)
  have hf : f =ᵐ[muH] (fun _ : Cfg => (1 : ℝ)) :=
    p4Q2PZ37ANV_actualPhysicalConstant_haarRepresentative H
  have hg : g =ᵐ[muH]
      (fun A : Cfg => (-2 : ℝ) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 A)) :=
    p4Q2PZ37ANV_actualPhysicalFirstGaussMode_haarRepresentative H
  have hfProd :
      (fun p : Cfg × Cfg => f p.1) =ᵐ[muH.prod muH]
        (fun _ => (1 : ℝ)) := by
    simpa only [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := muH) (ν := muH)).ae_eq hf
  have hgProd :
      (fun p : Cfg × Cfg => g p.2) =ᵐ[muH.prod muH]
        (fun p => (-2 : ℝ) *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)) := by
    simpa only [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := muH) (ν := muH)).ae_eq hg
  change realL2ExternalTensor f g =ᵐ[muH.prod muH] _
  filter_upwards [realL2ExternalTensor_coeFn f g, hfProd, hgProd]
    with p hTensor hfp hgp
  rw [hTensor]
  simp only [realL2ExternalTensorFunction, hfp, hgp, one_mul]


/-! ## ANV: the full original Wilson one-slab first Haar action moment

This uses the original pair of independent *link configurations*, not
independent plaquettes.  Both physical spatial halfweights, the genuine
temporal crossing action and the original first Gauss-law mode are kept.
The two-boundary Fubini calculation and the L² pairing are separated. -/

/-- The complete true original one-slab Wilson action has zero-coupling
Haar character pairing exactly -1/8 against the true primary spatial
character on its RIGHT boundary. The 1/2 right halfweight is essential:
the original left halfweight and temporal crossing terms cancel by
their already proved Haar identities. -/
theorem p4Q2PZ37ANV_originalOneSlab_firstCharacter_iteratedHaar
    (H : ℕ) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B *
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        -(1 / 8 : ℝ) := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let W := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
  let X := periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
  let vchar : Cfg → ℝ := fun B =>
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
  let wMean : ℝ := ∫ A : Cfg, W A ∂muH
  let c : ℝ := (1 / 2 : ℝ) * wMean + (Fintype.card Link : ℝ)
  letI : IsProbabilityMeasure muH := by
    dsimp [muH, periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hWCont : Continuous W :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hWInt : Integrable W muH :=
    hWCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- Avoid whnf on the complete configuration-space compactness instance:
  -- integrate each actual spatial link independently and then sum the
  -- finitely many original temporal crossing terms. This is the same
  -- original Haar factorization as the certified leftHaarMean theorem.
  have hXInt (B : Cfg) : Integrable (fun A : Cfg => X A B) muH := by
    let E := specialUnitaryWilsonPlaquetteEnergy 2
    have hMeasure : muH = Measure.pi (fun _ : Link => nu) := by
      change periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 =
        Measure.pi (fun _ : Link => nu)
      unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
      exact congrArg
        (fun i : Fintype Link =>
          letI : Fintype Link := i
          Measure.pi (fun _ : Link => nu))
        (Subsingleton.elim
          (oneSlabHaarL2SpatialLinkFintype H)
          (inferInstance : Fintype Link))
    have hEach (e : Link) :
        Integrable (fun a : G => E ((B e)⁻¹ * a)) nu := by
      have hCont : Continuous (fun a : G => E ((B e)⁻¹ * a)) :=
        (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
          (continuous_const.mul continuous_id)
      exact hCont.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hCoord (e : Link) :
        Integrable (fun A : Cfg => E ((B e)⁻¹ * A e))
          (Measure.pi (fun _ : Link => nu)) := by
      exact MeasureTheory.integrable_comp_eval
        (μ := fun _ : Link => nu) (i := e) (hEach e)
    have hSum : Integrable
        (fun A : Cfg => ∑ e : Link, E ((B e)⁻¹ * A e))
        (Measure.pi (fun _ : Link => nu)) := by
      exact integrable_finset_sum _ (fun e _ => hCoord e)
    have hAction (A : Cfg) :
        X A B = ∑ e : Link, E ((B e)⁻¹ * A e) := by
      rw [p4Q2PZ37ANV_originalCrossingAction_symmetric H A B]
      simp only [X, periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction,
        periodicHypercubicEvenSpatialSliceLinkList, Finset.sum_map_toList]
      apply Finset.sum_congr
      · ext e
        simp
      · intro e _
        rfl
    rw [hMeasure]
    refine hSum.congr ?_
    filter_upwards [] with A
    exact (hAction A).symm
  have hCharCont : Continuous vchar := by
    have heq :
        vchar =
          (fun B : Cfg =>
            GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
              (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
      funext B
      exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
    rw [heq]
    exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
      H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)
  have hCharInt : Integrable vchar muH :=
    hCharCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hWCharInt : Integrable (fun B : Cfg => W B * vchar B) muH :=
    (hWCont.mul hCharCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCharMean : (∫ B : Cfg, vchar B ∂muH) = 0 :=
    p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero H
  have hWCharMean :
      (∫ B : Cfg, W B * vchar B ∂muH) = -(1 / 4 : ℝ) :=
    p4Q2PZ37ANV_originalFullSpatialAction_primaryCharacter_haarPairing H
  have hActionMean (B : Cfg) :
      (∫ A : Cfg,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
          H 2 A B ∂muH) =
        c + (1 / 2 : ℝ) * W B := by
    have hRight :
        (∫ _A : Cfg, (1 / 2 : ℝ) * W B ∂muH) =
          (1 / 2 : ℝ) * W B := by simp
    calc
      _ = ∫ A : Cfg,
          ((1 / 2 : ℝ) * W A + X A B) + (1 / 2 : ℝ) * W B
          ∂muH := by rfl
      _ = (∫ A : Cfg, (1 / 2 : ℝ) * W A + X A B ∂muH) +
          (∫ _A : Cfg, (1 / 2 : ℝ) * W B ∂muH) :=
            integral_add ((hWInt.const_mul _).add (hXInt B)) (integrable_const _)
      _ = (1 / 2 : ℝ) * wMean +
          (∫ A : Cfg, X A B ∂muH) +
          (1 / 2 : ℝ) * W B := by
            rw [integral_add (hWInt.const_mul _) (hXInt B),
              integral_const_mul, hRight]
      _ = c + (1 / 2 : ℝ) * W B := by
            rw [p4Q2PZ37ANV_originalCrossingAction_leftHaarMean H B]
            rfl
  have hInner (B : Cfg) :
      (∫ A : Cfg,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
          H 2 A B * vchar B ∂muH) =
        (c + (1 / 2 : ℝ) * W B) * vchar B := by
    rw [integral_mul_const, hActionMean B]
  calc
    (∫ B : Cfg,
      (∫ A : Cfg,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B *
          vchar B ∂muH) ∂muH) =
      ∫ B : Cfg, (c + (1 / 2 : ℝ) * W B) * vchar B ∂muH := by
        apply integral_congr_ae
        filter_upwards [] with B
        exact hInner B
    _ = ∫ B : Cfg,
          c * vchar B + (1 / 2 : ℝ) * (W B * vchar B) ∂muH := by
        apply integral_congr_ae
        filter_upwards [] with B
        ring
    _ = c * (∫ B : Cfg, vchar B ∂muH) +
        (1 / 2 : ℝ) * (∫ B : Cfg, W B * vchar B ∂muH) := by
        rw [integral_add (hCharInt.const_mul _) (hWCharInt.const_mul _)]
        rw [integral_const_mul, integral_const_mul]
    _ = -(1 / 8 : ℝ) := by
        rw [hCharMean, hWCharMean]
        ring

/-- The ANU **original physical Gauss-law** pair-Haar action moment,
defined by the actual full one-slab action and the true first physical
Gram-Schmidt vector, is exactly 1/4 for every original finite even H,
including the length-two torus. This does not identify the completed OS
boundary operator or establish the continuum Yang-Mills mass gap. -/
theorem p4Q2PZ37ANV_originalFirstHaarActionMoment_eq_oneFourth
    (H : ℕ) :
    p4Q2PZ37ANU_originalFirstHaarActionMoment H = (1 / 4 : ℝ) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let muH := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let pairMu := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
  let S : Lp ℝ 2 pairMu := p4Q2PZ37ANT_originalSlabAction_pairHaarL2 H
  let f : Lp ℝ 2 muH :=
    ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
        Lp ℝ 2 muH)
  let g : Lp ℝ 2 muH :=
    ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
        PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
        Lp ℝ 2 muH)
  let T : Lp ℝ 2 pairMu := realL2ExternalTensor f g
  let raw : Cfg × Cfg → ℝ := fun p =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 p.1 p.2 *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)
  have hS : S =ᵐ[pairMu]
      (fun p : Cfg × Cfg =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
          H 2 p.1 p.2) :=
    p4Q2PZ37ANT_originalSlabAction_pairHaarL2_coeFn H
  have hT : T =ᵐ[pairMu]
      (fun p : Cfg × Cfg => (-2 : ℝ) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 p.2)) :=
    p4Q2PZ37ANV_actualFirstPhysicalTensor_pairHaarRepresentative H
  have hWCont :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hXCont :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous H 2
  have hSCont : Continuous
      (fun p : Cfg × Cfg =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
          H 2 p.1 p.2) := by
    dsimp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction]
    exact
      ((continuous_const.mul (hWCont.comp continuous_fst)).add hXCont).add
        (continuous_const.mul (hWCont.comp continuous_snd))
  have hCharCont :
      Continuous (fun B : Cfg =>
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) := by
    have heq :
        (fun B : Cfg =>
          Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)) =
        (fun B : Cfg =>
          GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
            (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
      funext B
      exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
    rw [heq]
    exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
      H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)
  have hRawInt : Integrable raw (muH.prod muH) := by
    have hRawCont : Continuous raw := hSCont.mul (hCharCont.comp continuous_snd)
    exact hRawCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change inner ℝ S T = (1 / 4 : ℝ)
  calc
    inner ℝ S T = ∫ p : Cfg × Cfg, raw p * (-2 : ℝ) ∂pairMu := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hS, hT] with p hs ht
      rw [hs, ht, periodicHypercubicEven_real_inner_eq_mul]
      dsimp [raw]
      ring
    _ = (-2 : ℝ) * (∫ p : Cfg × Cfg, raw p ∂pairMu) := by
      rw [integral_mul_const]
      ring
    _ = (-2 : ℝ) *
          (∫ B : Cfg,
            (∫ A : Cfg,
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
                H 2 A B *
                Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
              ∂muH) ∂muH) := by
        congr 1
        change (∫ p : Cfg × Cfg, raw p ∂(muH.prod muH)) = _
        simpa only [raw] using
          (MeasureTheory.integral_prod_symm raw hRawInt)
    _ = (1 / 4 : ℝ) := by
      rw [p4Q2PZ37ANV_originalOneSlab_firstCharacter_iteratedHaar H]
      ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalTimeZeroPrimaryPlaquetteHaar_integralTransport
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarMean_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalTimeZeroPrimaryCharacter_haarSecondMoment
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalTimeZeroPrimaryEnergyCharacter_haarPairing
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalRelativeLinkEnergy_haarMean_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalCrossingAction_rightHaarMean
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalCrossingAction_symmetric
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalCrossingAction_leftHaarMean
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_negativeIdentity_commutes
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalCharacter_centerFlip
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalWilsonGramSchmidtFirst_signedCentered

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryOriginOne_mem_support
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryOriginTwo_mem_support
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryOriginTwoLinks_unique_of_H_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryHasExclusiveLink_of_H_pos

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryOriginTwoLinks_unique_of_H_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryOriginTwoLinks_unique
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryHasExclusiveLink

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalCrossing_primaryCharacter_iteratedHaar_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalLeftSpatialAction_primaryCharacter_iteratedHaar_zero

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalPrimarySpatialEnergy_eq_cyclic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalNativePrimarySpatialEnergyCharacter_haarPairing

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_singleLinkCenterTwist_haarMeasurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_singleLinkCenterTwist_holonomy_of_not_mem
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_singleLinkCenterTwist_energy_of_not_mem

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalPlaquetteHolonomy_flip_fourth
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalPlaquetteCharacter_flip_fourth
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_primaryCharacter_originCenterFlip_odd
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_singleLinkCenterTwist_eq_existingPU
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_nonPrimarySpatialEnergy_primaryCharacter_haarOrthogonal

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalFullSpatialAction_primaryCharacter_haarPairing

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalFirstGramSchmidt_haarRepresentative
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_actualPhysicalFirstGaussMode_haarRepresentative
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_actualPhysicalConstant_haarRepresentative

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_actualFirstPhysicalTensor_pairHaarRepresentative

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalOneSlab_firstCharacter_iteratedHaar
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANV_originalFirstHaarActionMoment_eq_oneFourth
