import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2TimeOneHaarGramSchmidtCenteredV5_PZ37ANI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicTimeOneOSReflectionFormV5_PZ37ANF
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANJ — original closure-Haar time-one Wilson mode mean

ANI certifies that the original SU(2) Gram--Schmidt first continuous mode
is the Haar constant-one class and the second mode has Haar mean zero.
This leaf transports the SAME original literal time-one plaquette holonomy
from the actual boundary/positive-open-half product Haar measure through
the ANC closure coordinate equivalence, AMX time-one evaluation and AMS
physical spatial-slice cyclic plaquette holonomy.

The transport is valid for every finite H, including H=0, for the FULL
positive closure. It makes NO unproved claim about conditioning on a fixed
boundary at H=0 or H>0. Consequently a global Haar-mean result is not
silently identified with fiberwise vanishing or strict Wilson OS positivity.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANJ_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANJ_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANJ_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANJ_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANJ_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANJ_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance p4Q2PZ37ANJ_originalHaarProbability :
    IsProbabilityMeasure
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  infer_instance

local instance p4Q2PZ37ANJ_closureHaarFinite (H : ℕ) :
    IsFiniteMeasure
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- This is the literal single SU(2) holonomy used in ANC/ANF at time one,
without replacing the positive-closure boundary/open-half configuration. -/
noncomputable def p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy
    (H : ℕ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H 2) :
    Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
    ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H 2 z).1 (p4Q2PZ37AMX_positiveTimeOne H))

/-- The original full boundary/open-positive-half product Haar, NOT Gibbs
or the separate temporal-gauge half-path weight, pushes under the exact
time-one physical plaquette holonomy to the original normalized SU(2) Haar. -/
theorem p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy_measurePreserving
    (H : ℕ) :
    MeasurePreserving
      (p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H)
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  have hClosure :=
    p4Q2PZ37ANC_positiveClosureSpatialPath_measurePreserving H
  have hTime :=
    p4Q2PZ37AMX_positiveTimeOne_measurePreserving H
  have hPlaquette :=
    p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2
  simpa [p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy,
    Function.comp_def] using hPlaquette.comp (hTime.comp hClosure)

/-- The first chosen continuous SU(2) Wilson Gram--Schmidt mode has
original normalized-Haar mean one, using its certified L2 equality
with constant one, not an unproved pointwise choice identity. -/
theorem p4Q2PZ37ANJ_originalWilsonContinuousModeZero_haarMean_one :
    (∫ U, specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0 U
      ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))) = 1 := by
  let mu := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let f : SpecialUnitaryNormalizedHaarL2 2 :=
    ContinuousMap.toLp
      (E := ℝ) 2 mu ℝ
        (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0)
  have hRep :
      f =ᵐ[mu] specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞)) (μ := mu)
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0)
  have hF : f = Lp.const 2 mu (1 : ℝ) := by
    exact (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_toLp 0).trans
      p4Q2PZ37ANI_originalWilsonHaarGramSchmidtModeZero_eq_constOne
  have hOne :
      (Lp.const 2 mu (1 : ℝ)) =ᵐ[mu] (fun _ => (1 : ℝ)) := by
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (μ := mu) (p := (2 : ℝ≥0∞)) (c := (1 : ℝ)))
  calc
    (∫ U, specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0 U ∂mu) =
      ∫ U, f U ∂mu := integral_congr_ae hRep.symm
    _ = ∫ U, (Lp.const 2 mu (1 : ℝ)) U ∂mu := by rw [hF]
    _ = ∫ U, (1 : ℝ) ∂mu := integral_congr_ae hOne
    _ = 1 := by simp

/-- Exact global closure-Haar mean of either original time-one Wilson
Gram--Schmidt class-function mode. -/
theorem p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integral_eq_Haar
    (H k : ℕ) :
    (∫ z,
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H z)
      ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2))) =
      ∫ U, specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k U
        ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  let T := p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H
  let mu := (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
    (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
  let haar := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let f := specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
  have hMP : MeasurePreserving T mu haar := by
    simpa [T, mu, haar] using
      p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy_measurePreserving H
  change (∫ z, f (T z) ∂mu) = ∫ U, f U ∂haar
  calc
    (∫ z, f (T z) ∂mu) =
        ∫ U, f U ∂Measure.map T mu := by
      exact (MeasureTheory.integral_map
        hMP.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable).symm
    _ = ∫ U, f U ∂haar := by rw [hMP.map_eq]

/-- The first two original time-one mode averages are exactly 1 and 0
under the original shared-boundary times positive-open-half Haar product. -/
theorem p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeZero_integral_one
    (H : ℕ) :
    (∫ z,
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
        (p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H z)
      ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2))) = 1 := by
  rw [p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integral_eq_Haar]
  exact p4Q2PZ37ANJ_originalWilsonContinuousModeZero_haarMean_one

theorem p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeOne_integral_zero
    (H : ℕ) :
    (∫ z,
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
        (p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H z)
      ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2))) = 0 := by
  rw [p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integral_eq_Haar]
  exact p4Q2PZ37ANI_originalWilsonContinuousModeOne_haarMean_zero

/-- Integrability of each literal time-one SU(2) Wilson mode over the
original product Haar, derived from the actual bounded continuous mode,
without an additional L2/regularity assumption. -/
theorem p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integrable
    (H k : ℕ) :
    Integrable
      (fun z => specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
        (p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H z))
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)) := by
  let T := p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H
  let f := specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k
  have hMeas : Measurable (fun z => f (T z)) :=
    f.continuous.measurable.comp
      (p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy_measurePreserving H).measurable
  have hBound : ∀ z, ‖f (T z)‖ ≤ ‖f‖ := by
    intro z
    exact f.norm_coe_le_norm (T z)
  exact Integrable.of_bound hMeas.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall hBound)

/-- For every H including H=0, the unchanged original time-one two-mode
Wilson cylinder has exact ORIGINAL closure product-Haar mean c0.
The distinction between this joint mean and the fixed-boundary fiber
mean is retained, and no top-orthogonality of coefficients is used. -/
theorem p4Q2PZ37ANJ_originalTimeOneTwoMode_closureHaarMean_eq_c0
    (H : ℕ) (c0 c1 : ℝ) :
    (∫ z, p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1 z
      ∂((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2))) = c0 := by
  let T := p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy H
  let mu := (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
    (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
  let f0 := specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
  let f1 := specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
  have h0 : Integrable (fun z => f0 (T z)) mu :=
    p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integrable H 0
  have h1 : Integrable (fun z => f1 (T z)) mu :=
    p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integrable H 1
  change (∫ z, c0 * f0 (T z) + c1 * f1 (T z) ∂mu) = c0
  rw [integral_add (h0.const_mul c0) (h1.const_mul c1),
    integral_const_mul, integral_const_mul]
  rw [p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeZero_integral_one,
    p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeOne_integral_zero]
  ring

/-- The original beta-zero Wilson boundary Gram moment has a precisely
known first boundary-Haar moment. The actual finite Wilson partition
normalization is retained. This is not a fiberwise positivity statement. -/
theorem p4Q2PZ37ANJ_originalBetaZeroBoundaryGramMoment_boundaryHaarMean
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (c0 c1 : ℝ) :
    (∫ b,
      p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
        H 0 (by norm_num) c0 c1 b
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H 2)) =
    Real.sqrt
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) 0
        (by norm_num)).base.partitionFunction⁻¹) * c0 := by
  let f := p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H c0 c1
  let mu := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let nu := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  -- The named open-half Haar wrapper does not export an SFinite instance by
  -- mere local alias unfolding in the pinned integral_prod elaborator.
  -- Give Lean the finite-measure instance of this SAME original product Haar.
  letI : IsFiniteMeasure nu := by
    dsimp [nu, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  let M := |c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
    |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖
  let s := Real.sqrt
    ((periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) 0
      (by norm_num)).base.partitionFunction⁻¹)
  have hf : Measurable f :=
    p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_measurable H c0 c1
  have hBound : ∀ z, ‖f z‖ ≤ M := by
    intro z
    exact p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable_norm_le H c0 c1 z
  have hIntegrable : Integrable f (mu.prod nu) :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall hBound)
  change (∫ b, p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
    H 0 (by norm_num) c0 c1 b ∂mu) = s * c0
  calc
    (∫ b, p4Q2PZ37ANF_originalTimeOneWilsonBoundaryGramMoment
      H 0 (by norm_num) c0 c1 b ∂mu) =
      ∫ b, s * (∫ x, f (b, x) ∂nu) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with b
        exact p4Q2PZ37ANG0_originalTimeOneBoundaryMoment_eq_openHaarMean
          H c0 c1 b
    _ = s * (∫ b, ∫ x, f (b, x) ∂nu ∂mu) := by
      rw [integral_const_mul]
    _ = s * (∫ z, f z ∂mu.prod nu) := by
      congr 1
      exact (MeasureTheory.integral_prod _ hIntegrable).symm
    _ = s * c0 := by
      rw [p4Q2PZ37ANJ_originalTimeOneTwoMode_closureHaarMean_eq_c0]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalPositiveClosureTimeOneHolonomy_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalWilsonContinuousModeZero_haarMean_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integral_eq_Haar
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeZero_integral_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalPositiveClosureTimeOneModeOne_integral_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalPositiveClosureTimeOneMode_integrable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalTimeOneTwoMode_closureHaarMean_eq_c0
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalBetaZeroBoundaryGramMoment_boundaryHaarMean
