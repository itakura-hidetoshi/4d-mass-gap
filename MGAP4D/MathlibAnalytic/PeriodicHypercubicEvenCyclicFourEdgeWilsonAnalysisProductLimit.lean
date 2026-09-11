import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveCyclicProbeIntegralLimit
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFockProbeWilsonAnalysisFubini
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProduct InnerProductSpace Topology

noncomputable section

private theorem cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeWilsonAnalysisProductLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeWilsonAnalysisProductLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeWilsonAnalysisProductLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeWilsonAnalysisProductLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeWilsonAnalysisProductLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeWilsonAnalysisProductLimitSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

local instance cyclicFourEdgeWilsonAnalysisProductLimitBoundaryHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance cyclicFourEdgeWilsonAnalysisProductLimitOpenHalfHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance cyclicFourEdgeWilsonAnalysisProductLimitProductHaarFinite (H : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenBoundaryOpenHalfHaarMeasure]
  infer_instance

/-- Boundary-fibered assembly is jointly measurable in the boundary and
positive-open-half coordinates when the negative half is fixed. -/
private theorem periodicHypercubicEvenBoundaryFiberedAssemble_pair_measurable
    (H : ℕ)
    (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          p.1 p.2 y) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ
  have hz : Measurable
      (fun p : P.BoundaryConfiguration Gauge × P.OpenHalfConfiguration Gauge =>
        (p.1, (p.2, y))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have hsymm : Measurable
      (fun z : P.BoundaryConfiguration Gauge ×
          (P.OpenHalfConfiguration Gauge × P.OpenHalfConfiguration Gauge) =>
        (P.boundaryFiberedPiMeasurableEquiv Gauge).symm z) :=
    (P.boundaryFiberedPiMeasurableEquiv Gauge).symm.measurable
  simpa [P, Gauge] using hsymm.comp hz

/-- Every actual plaquette holonomy is jointly measurable in the boundary and
positive-open-half coordinates with the negative half fixed. -/
private theorem periodicHypercubicEvenBoundaryFiberedPlaquetteHolonomy_pair_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2)
    (p : PeriodicHypercubicEvenPlaquette H) :
    Measurable
      (fun z :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
            z.1 z.2 y) p) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2
    cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive beta hbeta
  have hfull := continuous_compact_oriented_plaquetteHolonomy C p
  have hfull' : Continuous
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin 2) ℂ =>
        periodicHypercubicPlaquetteHolonomy A p) := by
    simpa [C] using hfull
  exact hfull'.measurable.comp
    (periodicHypercubicEvenBoundaryFiberedAssemble_pair_measurable H y)

/-- The selected temporal-companion normalized trace is jointly measurable in
boundary and positive-open-half coordinates. -/
private theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_pair_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2)
    (k : Fin 4) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
          H p.1 p.2 y k) := by
  have henergy := continuous_specialUnitaryWilsonPlaquetteEnergy 2
  have htrace : Continuous
      (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
        normalizedSpecialUnitaryRealTrace 2 U) := by
    have h : Continuous
        (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
          (1 : ℝ) - specialUnitaryWilsonPlaquetteEnergy 2 U) :=
      continuous_const.sub henergy
    simpa [specialUnitaryWilsonPlaquetteEnergy_eq] using h
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
  exact htrace.measurable.comp
    (periodicHypercubicEvenBoundaryFiberedPlaquetteHolonomy_pair_measurable
      H beta hbeta y
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

/-- Each finite actual-trace Taylor factor is jointly measurable. -/
private theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_pair_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2)
    (k : Fin 4) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor
          H beta degree p.1 p.2 y k) := by
  have htrace :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_pair_measurable
      H beta hbeta y k
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor
  exact measurable_const.mul
    (Finset.measurable_sum _ fun m _ =>
      ((measurable_const.mul htrace).pow_const m).div_const
        (Nat.factorial m : ℝ))

/-- The complete four-factor rectangular Taylor product is jointly measurable. -/
private theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct_pair_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct
          H beta degree p.1 p.2 y) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct
  exact
    ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_pair_measurable
        H beta hbeta degree y 2).mul
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_pair_measurable
        H beta hbeta degree y 3)).mul
    ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_pair_measurable
        H beta hbeta degree y 0).mul
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_pair_measurable
        H beta hbeta degree y 1))

/-- The literal product of the four selected Wilson factors is jointly
measurable in boundary and positive-open-half coordinates. -/
private theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct_pair_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
          H beta p.1 p.2 y) := by
  have hfactor (k : Fin 4) : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        specialUnitaryWilsonBoltzmannCentralFunction 2 beta
          (periodicHypercubicPlaquetteHolonomy
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
              p.1 p.2 y)
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :=
    (continuous_specialUnitaryWilsonBoltzmannCentralFunction 2 beta).measurable.comp
      (periodicHypercubicEvenBoundaryFiberedPlaquetteHolonomy_pair_measurable
        H beta hbeta y
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
  exact ((hfactor 2).mul (hfactor 3)).mul ((hfactor 0).mul (hfactor 1))

/-- The exact residual completed-positive Gram factor is jointly measurable.
It is recovered as the actual Gram feature divided by the strictly positive
product of the four selected Wilson factors; no complement-action identity is
assumed. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_jointMeasurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
          H beta hbeta p.1 p.2) := by
  let y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 :=
    fun _ => 1
  have hgram :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
      H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive beta hbeta
  have hfour :=
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct_pair_measurable
      H beta hbeta y
  have heq :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
          H beta hbeta p.1 p.2) =
        fun p =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive
              beta hbeta p.1 p.2 /
            periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
              H beta p.1 p.2 y := by
    funext p
    have hpos :
        0 < periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
          H beta p.1 p.2 y := by
      unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
      unfold specialUnitaryWilsonBoltzmannCentralFunction
      positivity
    apply (eq_div_iff hpos.ne').2
    exact
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_residual_mul_fourCompanionProduct
        H beta hbeta p.1 p.2).symm
  rw [heq]
  exact hgram.div hfour

/-- The full independent four-edge finite Wilson kernel is jointly measurable
on boundary × open-half Haar. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialKernel_jointMeasurable
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord
            H p.1)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord
            H p.2)) := by
  let y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 :=
    fun _ => 1
  have hactual :=
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct_pair_measurable
      H beta hbeta degree y
  have heq :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord
            H p.1)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord
            H p.2)) =
        fun p =>
          periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct
            H beta degree p.1 p.2 y := by
    funext p
    exact
      periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialKernel_eq_product_actualTraceSums
        hH beta degree p.1 p.2 y
  rw [heq]
  exact hactual

/-- Every complete finite four-edge Wilson approximation to the actual
completed-positive Gram feature is jointly measurable. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_jointMeasurable
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
          H beta hbeta degree p.1 p.2) := by
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
  exact
    (periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_jointMeasurable
      H beta hbeta).mul
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialKernel_jointMeasurable
      hH beta hbeta degree)

/-- Product-Haar matrix coefficient of the complete finite four-edge Wilson
Taylor/Fock approximation against a boundary `L²` vector and the actual cyclic
open-half `L²` probe. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) : ℝ :=
  ∫ p,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree p.1 p.2 *
      (f p.1 *
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q p.2)
    ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2)

/-- Product-Haar matrix coefficient of the actual completed-positive Wilson
Gram feature against the same boundary and cyclic open-half `L²` vectors. -/
noncomputable def
    periodicHypercubicEvenBoundaryCompletedPositiveGramCyclicProbeProductIntegral
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) : ℝ :=
  ∫ p,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive
        beta hbeta p.1 p.2 *
      (f p.1 *
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q p.2)
    ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2)

/-- The complete rectangular four-edge Taylor/Fock approximation converges
through the full boundary × open-half Haar pairing.  The dominating function
is the exact degree-independent Gram bound times the external tensor of the
two `L²` vectors, so no diagonal-sector or transport-defect assumption enters. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral_tendsto
    {H : ℕ}
    (hH : 0 < H)
    (n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral
          H n beta hbeta degree f q)
      atTop
      (𝓝
        (periodicHypercubicEvenBoundaryCompletedPositiveGramCyclicProbeProductIntegral
          H n beta hbeta f q)) := by
  let g :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q
  let C := periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialBound
    H beta hbeta
  have hfg : Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
        f p.1 * g p.2)
      (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H 2) := by
    have hmem := realL2ExternalTensorFunction_memLp_two f g
    have hint := hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa [realL2ExternalTensorFunction,
      periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using hint
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramCyclicProbeProductIntegral
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun p => C * ‖f p.1 * g p.2‖)
  · exact Filter.Eventually.of_forall fun degree =>
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_jointMeasurable
        hH beta hbeta degree).aestronglyMeasurable.mul hfg.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun degree =>
      Filter.Eventually.of_forall fun p => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_abs_le
            H beta hbeta degree p.1 p.2)
          (norm_nonneg (f p.1 * g p.2))
  · simpa [C] using hfg.norm.const_mul C
  · exact Filter.Eventually.of_forall fun p =>
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_tendsto
        hH beta hbeta p.1 p.2).mul tendsto_const_nhds

/-- The actual product-Haar integral is exactly the #1662 Wilson analysis
matrix coefficient. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramCyclicProbeProductIntegral_eq_inner_analysis
    (H n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    periodicHypercubicEvenBoundaryCompletedPositiveGramCyclicProbeProductIntegral
        H n beta hbeta f q =
      inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive beta hbeta f) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H 2
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H 2
  let g :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
      H n q
  let raw := fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2 =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive
      beta hbeta p.1 p.2 * (f p.1 * g p.2)
  have hraw : Integrable raw (boundaryMeasure.prod halfMeasure) := by
    simpa [raw, boundaryMeasure, halfMeasure, g] using
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_weightedPair_integrable
        H n beta hbeta q f
  calc
    periodicHypercubicEvenBoundaryCompletedPositiveGramCyclicProbeProductIntegral
        H n beta hbeta f q =
      ∫ p, raw p ∂(boundaryMeasure.prod halfMeasure) := by
        rfl
    _ = ∫ b, ∫ x, raw (b, x) ∂halfMeasure ∂boundaryMeasure := by
      exact MeasureTheory.integral_prod raw hraw
    _ = ∫ b, ∫ x,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive
            beta hbeta b x *
          (f b *
            periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
              H n q x)
        ∂halfMeasure ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards with b
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_coeFn
          H n q] with x hx
      simp only [raw]
      rw [show g x =
          periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
            H n q x by exact hx]
    _ = inner ℝ
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
          H n q)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive beta hbeta f) := by
      symm
      simpa [boundaryMeasure, halfMeasure] using
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2_inner_analysis_eq_iteratedIntegral
          H n beta hbeta q f

/-- Full four-edge Wilson Taylor/Fock product-Haar convergence lands directly
on the actual finite-Wilson analysis matrix coefficient. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral_tendsto_inner_analysis
    {H : ℕ}
    (hH : 0 < H)
    (n : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H 2))
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert) :
    Tendsto
      (fun degree =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral
          H n beta hbeta degree f q)
      atTop
      (𝓝
        (inner ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeL2
            H n q)
          (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
            H 2 cyclicFourEdgeWilsonAnalysisProductLimitTwoRankPositive beta hbeta f))) := by
  have h :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartialCyclicProbeProductIntegral_tendsto
      hH n beta hbeta f q
  simpa only [
    periodicHypercubicEvenBoundaryCompletedPositiveGramCyclicProbeProductIntegral_eq_inner_analysis]
    using h

end

end MathlibAnalytic
end MGAP4D
