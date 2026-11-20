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
