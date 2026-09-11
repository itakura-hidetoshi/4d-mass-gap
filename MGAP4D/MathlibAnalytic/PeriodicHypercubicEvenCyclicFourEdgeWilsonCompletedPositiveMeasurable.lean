import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeWilsonCompletedPositiveBound
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasurableEquivSymm
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureMeasurability

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem cyclicFourEdgeCompletedPositiveMeasurableTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance cyclicFourEdgeCompletedPositiveMeasurableTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance cyclicFourEdgeCompletedPositiveMeasurableCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance cyclicFourEdgeCompletedPositiveMeasurableSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance cyclicFourEdgeCompletedPositiveMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance cyclicFourEdgeCompletedPositiveMeasurableBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance cyclicFourEdgeCompletedPositiveMeasurableSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- With boundary and negative half fixed, geometric boundary-fibered assembly
is measurable in the positive open-half coordinate. -/
private theorem periodicHypercubicEvenBoundaryFiberedAssemble_openHalf_measurable
    (H : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Measurable
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
        (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ
  have hz : Measurable
      (fun x : P.OpenHalfConfiguration Gauge => (b, (x, y))) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have hsymm : Measurable
      (fun z : P.BoundaryConfiguration Gauge ×
          (P.OpenHalfConfiguration Gauge × P.OpenHalfConfiguration Gauge) =>
        (P.boundaryFiberedPiMeasurableEquiv Gauge).symm z) :=
    (P.boundaryFiberedPiMeasurableEquiv Gauge).symm.measurable
  simpa [P, Gauge] using hsymm.comp hz

/-- For fixed boundary and negative-half coordinates, every actual periodic
plaquette holonomy is measurable in the positive open-half coordinate. -/
private theorem periodicHypercubicEvenBoundaryFiberedPlaquetteHolonomy_openHalf_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (p : PeriodicHypercubicEvenPlaquette H) :
    Measurable
      (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
        periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) p) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) 2
    cyclicFourEdgeCompletedPositiveMeasurableTwoRankPositive beta hbeta
  have hfull := continuous_compact_oriented_plaquetteHolonomy C p
  have hfull' : Continuous
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin 2) ℂ =>
        periodicHypercubicPlaquetteHolonomy A p) := by
    simpa [C] using hfull
  exact hfull'.measurable.comp
    (periodicHypercubicEvenBoundaryFiberedAssemble_openHalf_measurable H b y)

/-- The literal normalized trace of each selected temporal-companion plaquette
is measurable in the actual positive open-half coordinate. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    Measurable
      (fun x =>
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace
          H b x y k) := by
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
    (periodicHypercubicEvenBoundaryFiberedPlaquetteHolonomy_openHalf_measurable
      H beta hbeta b y
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

/-- Each finite literal-trace Taylor factor is measurable. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (k : Fin 4) :
    Measurable
      (fun x =>
        periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor
          H beta degree b x y k) := by
  have htrace :=
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionNormalizedTrace_measurable
      H beta hbeta b y k
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor
  exact measurable_const.mul
    (Finset.measurable_sum _ fun m _ =>
      ((measurable_const.mul htrace).pow_const m).div_const (Nat.factorial m : ℝ))

/-- The full rectangular four-factor finite Taylor product is measurable in the
actual positive open-half coordinate. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Measurable
      (fun x =>
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct
          H beta degree b x y) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct
  exact
    ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_measurable
        H beta hbeta degree b y 2).mul
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_measurable
        H beta hbeta degree b y 3)).mul
    ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_measurable
        H beta hbeta degree b y 0).mul
      (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionActualTraceTaylorPartialFactor_measurable
        H beta hbeta degree b y 1))

/-- The literal product of the four selected actual Wilson Boltzmann factors is
measurable in the positive open-half coordinate. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct_measurable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Measurable
      (fun x =>
        periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
          H beta b x y) := by
  have hfactor (k : Fin 4) : Measurable
      (fun x =>
        specialUnitaryWilsonBoltzmannCentralFunction 2 beta
          (periodicHypercubicPlaquetteHolonomy
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :=
    (continuous_specialUnitaryWilsonBoltzmannCentralFunction 2 beta).measurable.comp
      (periodicHypercubicEvenBoundaryFiberedPlaquetteHolonomy_openHalf_measurable
        H beta hbeta b y
        (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
  exact ((hfactor 2).mul (hfactor 3)).mul ((hfactor 0).mul (hfactor 1))

/-- The exact residual completed-positive Gram factor is measurable.  This is
proved from the already-measurable actual Gram feature divided by the strictly
positive product of the four extracted Wilson factors, so no measurable
complement-action representation is assumed. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_measurable
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Measurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor
        H beta hbeta b) := by
  let y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) := fun _ => 1
  have hgram := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_measurable
    H 2 cyclicFourEdgeCompletedPositiveMeasurableTwoRankPositive beta hbeta b
  have hfour :=
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct_measurable
      H beta hbeta b y
  have heq :
      periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor H beta hbeta b =
        fun x =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H 2 cyclicFourEdgeCompletedPositiveMeasurableTwoRankPositive beta hbeta b x /
            periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
              H beta b x y := by
    funext x
    have hpos :
        0 < periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
          H beta b x y := by
      unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionWilsonBoltzmannProduct
      unfold specialUnitaryWilsonBoltzmannCentralFunction
      positivity
    apply (eq_div_iff hpos.ne').2
    exact
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_residual_mul_fourCompanionProduct
        H beta hbeta b x).symm
  rw [heq]
  exact hgram.div hfour

/-- For every fixed boundary configuration, every complete finite four-edge
Taylor/Fock approximation to the completed-positive Gram feature is measurable. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial_measurable
    {H : ℕ}
    (hH : 0 < H)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Measurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
        H beta hbeta degree b) := by
  let y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) := fun _ => 1
  have hres :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramResidualFactor_measurable
      hH beta hbeta b
  have hpartialActual :=
    periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct_measurable
      H beta hbeta degree b y
  have hpartialKernel : Measurable
      (fun x =>
        specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
          (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)) := by
    have heq :
        (fun x =>
          specialUnitaryTwoCyclicFourEdgeWilsonPartialProductKernel beta degree
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeWord H x)) =
          fun x =>
            periodicHypercubicEvenPrimarySpatialPlaquetteFourTemporalCompanionActualTraceTaylorPartialProduct
              H beta degree b x y := by
      funext x
      exact
        periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfFourEdgeWilsonPartialKernel_eq_product_actualTraceSums
          hH beta degree b x y
    rw [heq]
    exact hpartialActual
  unfold periodicHypercubicEvenBoundaryCompletedPositiveGramFourEdgeWilsonPartial
  exact hres.mul hpartialKernel

end

end MathlibAnalytic
end MGAP4D
