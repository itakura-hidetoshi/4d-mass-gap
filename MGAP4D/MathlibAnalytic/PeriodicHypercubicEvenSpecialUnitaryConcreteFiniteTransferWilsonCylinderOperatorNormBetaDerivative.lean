import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderBetaDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open scoped BigOperators InnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 2000000

local instance wilsonCylinderOperatorNormBetaDerivativeSpatialSliceVertexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceVertex H) := Fintype.ofFinite _
local instance wilsonCylinderOperatorNormBetaDerivativeSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance wilsonCylinderOperatorNormBetaDerivativeSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance wilsonCylinderOperatorNormBetaDerivativeSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance wilsonCylinderOperatorNormBetaDerivativeSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance wilsonCylinderOperatorNormBetaDerivativeSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance wilsonCylinderOperatorNormBetaDerivativeSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The uniform Wilson path-action bound is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg
    (H N : ℕ) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
  positivity

/-- On the physical half-line, the literal Wilson path kernel is Lipschitz in beta,
with Lipschitz coefficient given by the beta-independent path-action bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_norm_sub_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N gamma path -
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N * ‖gamma - beta‖ := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N
  let S :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  let K := fun t : ℝ =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path
  let dK := fun t : ℝ => -S * K t
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt K (dK t) (Ici (0 : ℝ)) t := by
    intro t ht
    have h :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_hasDerivAt_beta
        H N t path
    simpa [K, dK, S] using h.hasDerivWithinAt
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg
        H N
  have hS : ‖S‖ ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
        H N path
  have hbound : ∀ t ∈ Ici (0 : ℝ), ‖dK t‖ ≤ C := by
    intro t ht
    have hKt : |K t| ≤ 1 := by
      simpa [K] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
          H N hN t ht path
    calc
      ‖dK t‖ = ‖S‖ * |K t| := by
        simp [dK, Real.norm_eq_abs]
      _ ≤ C * 1 := mul_le_mul hS hKt (abs_nonneg _) hC
      _ = C := by ring
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Ici (0 : ℝ)) hbeta hgamma
  simpa [K, C] using hmvt

/-- Pointwise first-order Taylor remainder for the positive-half Wilson path kernel.
The path-action bound makes the remainder quadratic, uniformly on the finite path carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_quadraticRemainder
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : ℝ)
    (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N gamma path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path +
        (gamma - beta) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
              H N path)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma - beta‖ ^ 2 := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N
  let S :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path
  let K := fun t : ℝ =>
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N t path
  let dK := fun t : ℝ => -S * K t
  let R := fun t : ℝ => K t - K beta - (t - beta) * dK beta
  have hC : 0 ≤ C := by
    simpa [C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound_nonneg
        H N
  have hS : ‖S‖ ≤ C := by
    simpa [S, C] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
        H N path
  have hderiv : ∀ t ∈ uIcc beta gamma,
      HasDerivWithinAt R (dK t - dK beta) (uIcc beta gamma) t := by
    intro t ht
    have hK :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_hasDerivAt_beta
        H N t path
    have hlin := (hasDerivAt_id t).sub_const beta
    have hR := (hK.sub_const (K beta)).sub (hlin.mul_const (dK beta))
    convert hR.hasDerivWithinAt using 1 <;> simp [R, K, dK, S] <;> ring
  have hbound : ∀ t ∈ uIcc beta gamma,
      ‖dK t - dK beta‖ ≤ C ^ 2 * ‖gamma - beta‖ := by
    intro t ht
    have ht_nonneg : 0 ≤ t := by
      change min beta gamma ≤ t ∧ t ≤ max beta gamma at ht
      have hmin : 0 ≤ min beta gamma := le_min hbeta hgamma
      exact hmin.trans ht.1
    have hKlip :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_norm_sub_le
        H N hN beta t hbeta ht_nonneg path
    have hdist : ‖t - beta‖ ≤ ‖gamma - beta‖ := by
      have hd := Real.dist_left_le_of_mem_uIcc ht
      simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using hd
    have hdK : ‖dK t - dK beta‖ ≤ C ^ 2 * ‖t - beta‖ := by
      calc
        ‖dK t - dK beta‖ = ‖S‖ * ‖K t - K beta‖ := by
          rw [show dK t - dK beta = -S * (K t - K beta) by
            simp [dK]
            ring]
          simp
        _ ≤ C * ‖K t - K beta‖ :=
          mul_le_mul_of_nonneg_right hS (norm_nonneg _)
        _ ≤ C * (C * ‖t - beta‖) :=
          mul_le_mul_of_nonneg_left (by simpa [K, C] using hKlip) hC
        _ = C ^ 2 * ‖t - beta‖ := by ring
    exact hdK.trans (mul_le_mul_of_nonneg_left hdist (sq_nonneg C))
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_uIcc beta gamma) left_mem_uIcc right_mem_uIcc
  convert hmvt using 1 <;> simp [R, dK, K, S, C] <;> ring

/-- The two endpoint L2 states have an L1 product on the common product-Haar path carrier. -/
private theorem wilsonCylinderOperatorNormBetaDerivative_endpointProduct_integrable
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  have hzero : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (0 : Fin (n + 1))) pathMu mu := by
    simpa [pathMu, mu, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => mu) (0 : Fin (n + 1)))
  have hlast : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (Fin.last n)) pathMu mu := by
    simpa [pathMu, mu, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => mu) (Fin.last n))
  have hf2 : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)) 2 pathMu := by
    simpa [Function.comp_def, n] using
      (Lp.memLp (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        hzero
  have hg2 : MemLp
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last n))) 2 pathMu := by
    simpa [Function.comp_def, n] using
      (Lp.memLp (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        hlast
  rw [← memLp_one_iff_integrable]
  simpa [n] using hg2.mul' hf2

/-- Quantitative endpoint Holder estimate on the product-Haar path carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    (∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N)) ≤
      ‖f‖ * ‖g‖ := by
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let n := periodicHypercubicEvenPositiveHalfCylinderSlabCount H
  let f0 := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0)
  let g1 := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path (Fin.last n))
  have hzero : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (0 : Fin (n + 1))) pathMu mu := by
    simpa [pathMu, mu, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => mu) (0 : Fin (n + 1)))
  have hlast : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        path (Fin.last n)) pathMu mu := by
    simpa [pathMu, mu, n,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (n + 1) => mu) (Fin.last n))
  have hf2 : MemLp f0 2 pathMu := by
    simpa [f0, Function.comp_def, n] using
      (Lp.memLp (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        hzero
  have hg2 : MemLp g1 2 pathMu := by
    simpa [g1, Function.comp_def, n] using
      (Lp.memLp (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)).comp_measurePreserving
        hlast
  have hbase : Integrable (fun path => f0 path * g1 path) pathMu := by
    rw [← memLp_one_iff_integrable]
    exact hg2.mul' hf2
  have hholder :
      eLpNorm (fun path => f0 path * g1 path) 1 pathMu ≤
        eLpNorm f0 2 pathMu * eLpNorm g1 2 pathMu := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        hf2.1 hg2.1 (fun x y : ℝ => x * y) 1
        (Filter.Eventually.of_forall fun _ => by simp))
  have htop : eLpNorm f0 2 pathMu * eLpNorm g1 2 pathMu ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.mul_ne_top hf2.2.ne hg2.2.ne
  have hfNorm : (eLpNorm f0 2 pathMu).toReal = ‖f‖ := by
    calc
      (eLpNorm f0 2 pathMu).toReal =
          (eLpNorm (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) 2 mu).toReal := by
        congr 1
        simpa [f0, Function.comp_def, n] using
          (eLpNorm_comp_measurePreserving
            (p := (2 : ℝ≥0∞))
            (Lp.aestronglyMeasurable
              (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)) hzero)
      _ = ‖(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)‖ :=
        (Lp.norm_def _).symm
      _ = ‖f‖ := rfl
  have hgNorm : (eLpNorm g1 2 pathMu).toReal = ‖g‖ := by
    calc
      (eLpNorm g1 2 pathMu).toReal =
          (eLpNorm (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) 2 mu).toReal := by
        congr 1
        simpa [g1, Function.comp_def, n] using
          (eLpNorm_comp_measurePreserving
            (p := (2 : ℝ≥0∞))
            (Lp.aestronglyMeasurable
              (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)) hlast)
      _ = ‖(g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)‖ :=
        (Lp.norm_def _).symm
      _ = ‖g‖ := rfl
  calc
    (∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ∂pathMu) =
        (eLpNorm (fun path => f0 path * g1 path) 1 pathMu).toReal := by
      change (∫ path, ‖f0 path * g1 path‖ ∂pathMu) =
        (eLpNorm (fun path => f0 path * g1 path) 1 pathMu).toReal
      rw [integral_norm_eq_lintegral_enorm hbase.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm]
    _ ≤ (eLpNorm f0 2 pathMu * eLpNorm g1 2 pathMu).toReal :=
      ENNReal.toReal_mono htop hholder
    _ = ‖f‖ * ‖g‖ := by rw [ENNReal.toReal_mul, hfNorm, hgNorm]

/-- Endpoint integrability with one nonnegative-beta Wilson path kernel. -/
private theorem wilsonCylinderOperatorNormBetaDerivative_endpointIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  have hbase : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    simpa [pathMu] using
      wilsonCylinderOperatorNormBetaDerivative_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta)
      pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := hbase.aestronglyMeasurable.mul hKmeas
    simpa [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using h
  apply hbase.mono hmeas
  filter_upwards with path
  rw [show
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
      ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path by ring,
    norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (by simpa [Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
        H N hN beta hbeta path)

/-- Endpoint integrability with the complete Wilson path action inserted. -/
private theorem wilsonCylinderOperatorNormBetaDerivative_actionIntegrand_integrable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N
  have hbase : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    simpa [pathMu] using
      wilsonCylinderOperatorNormBetaDerivative_endpointProduct_integrable H N f g
  have hKmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta)
      pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H N beta).aestronglyMeasurable
  have hSmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N)
      pathMu :=
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_measurable
      H N).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
            H N path *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) pathMu := by
    have h := (hbase.aestronglyMeasurable.mul hKmeas).mul hSmeas
    simpa [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using h
  have hdom : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
        C * |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul C
  apply hdom.mono' hmeas
  filter_upwards with path
  have hK :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      H N hN beta hbeta path
  have hS :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction_norm_le_uniformBound
      H N path
  change
    |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
      C * |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))|
  rw [show
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
      ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))) *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path) by ring,
    abs_mul, abs_mul]
  have hKS :
      |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path| *
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path| ≤ C := by
    calc
      _ ≤ 1 * C := mul_le_mul hK (by simpa [Real.norm_eq_abs, C] using hS)
        (abs_nonneg _) (by positivity)
      _ = C := by ring
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hKS
      (abs_nonneg
        ((f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))))

/-- Physical operator remainder after subtracting the first-order Wilson-action variation. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
      H N hN gamma hgamma -
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
      H N hN beta hbeta +
    (gamma - beta) •
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
        H N hN beta hbeta

/-- Matrix coefficients of the physical remainder are literally the endpoint-weighted
pointwise Wilson-kernel Taylor remainder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_inner_eq_integral
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
          H N hN beta hbeta gamma hgamma f) g =
      ∫ path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N,
        (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N gamma path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path +
            (gamma - beta) *
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                  H N beta path *
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
                  H N path)) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let F := fun t : ℝ =>
    fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N t path *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let A := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H N beta path *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction H N path *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hFgamma : Integrable (F gamma) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderOperatorNormBetaDerivative_endpointIntegrand_integrable
        H N hN gamma hgamma f g
  have hFbeta : Integrable (F beta) pathMu := by
    simpa [F, pathMu] using
      wilsonCylinderOperatorNormBetaDerivative_endpointIntegrand_integrable
        H N hN beta hbeta f g
  have hA : Integrable A pathMu := by
    simpa [A, pathMu] using
      wilsonCylinderOperatorNormBetaDerivative_actionIntegrand_integrable
        H N hN beta hbeta f g
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
  change
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN gamma hgamma f -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          H N hN beta hbeta f +
        (gamma - beta) •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN beta hbeta f) g = _
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransfer_inner
      H N hN gamma hgamma f g]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude_eq_physicalTransfer_inner
      H N hN beta hbeta f g]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator_inner_eq_pathActionIntegral
      H N hN beta hbeta f g]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeEndpointAmplitude
  change
    (∫ path, F gamma path ∂pathMu) - (∫ path, F beta path ∂pathMu) +
        (gamma - beta) * (∫ path, A path ∂pathMu) = _
  rw [← integral_sub hFgamma hFbeta, ← integral_const_mul]
  rw [← integral_add (hFgamma.sub hFbeta) (hA.const_mul (gamma - beta))]
  apply integral_congr_ae
  filter_upwards with path
  simp [F, A]
  ring

/-- Uniform matrix-coefficient estimate for the physical beta remainder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_inner_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f g : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
          H N hN beta hbeta gamma hgamma f) g‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma - beta‖ ^ 2 * ‖f‖ * ‖g‖ := by
  let pathMu := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N
  let C :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
      H N
  let B := C ^ 2 * ‖gamma - beta‖ ^ 2
  let base := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  let rem := fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N =>
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N gamma path -
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          H N beta path +
        (gamma - beta) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
              H N path)) *
      (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
        (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
  have hbase : Integrable base pathMu := by
    simpa [base, pathMu] using
      wilsonCylinderOperatorNormBetaDerivative_endpointProduct_integrable H N f g
  have hB : 0 ≤ B := by positivity
  have hdom : Integrable (fun path => B * |base path|) pathMu := by
    simpa [Pi.smul_apply, smul_eq_mul] using hbase.norm.smul B
  have hpoint : ∀ path, ‖rem path‖ ≤ B * |base path| := by
    intro path
    have hrem :=
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_quadraticRemainder
        H N hN beta gamma hbeta hgamma path
    change
      |(f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N gamma path -
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            H N beta path +
          (gamma - beta) *
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                H N beta path *
              periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
                H N path)) *
        (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
          (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))| ≤
        B * |base path|
    rw [show
      (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N) (path 0) *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N gamma path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path +
            (gamma - beta) *
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                  H N beta path *
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
                  H N path)) *
          (g : PeriodicHypercubicEvenSpecialUnitaryTransferWordHaarL2 H N)
            (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H))) =
        base path *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N gamma path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path +
            (gamma - beta) *
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                  H N beta path *
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
                  H N path)) by simp [base]; ring,
      abs_mul]
    have hrem' :
        |periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N gamma path -
            periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
              H N beta path +
            (gamma - beta) *
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
                  H N beta path *
                periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathAction
                  H N path)| ≤ B := by
      simpa [Real.norm_eq_abs, B, C] using hrem
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hrem' (abs_nonneg (base path))
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_inner_eq_integral
    H N hN beta hbeta gamma hgamma f g]
  change ‖∫ path, rem path ∂pathMu‖ ≤ _
  have hint := norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpoint)
  calc
    ‖∫ path, rem path ∂pathMu‖ ≤ ∫ path, B * |base path| ∂pathMu := hint
    _ = B * (∫ path, |base path| ∂pathMu) := by
      exact integral_const_mul B (fun path => |base path|)
    _ ≤ B * (‖f‖ * ‖g‖) := by
      apply mul_le_mul_of_nonneg_left _ hB
      simpa [base, pathMu] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderEndpointProduct_integral_abs_le
          H N f g
    _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma - beta‖ ^ 2 * ‖f‖ * ‖g‖ := by
      simp [B, C]
      ring

/-- Pointwise operator bound obtained from the uniform matrix-coefficient estimate
by testing against the image vector itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_apply_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
        H N hN beta hbeta gamma hgamma f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma - beta‖ ^ 2) * ‖f‖ := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
      H N hN beta hbeta gamma hgamma
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 * ‖gamma - beta‖ ^ 2
  have hB : 0 ≤ B := by positivity
  have hinner :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_inner_norm_le
      H N hN beta hbeta gamma hgamma f (R f)
  have hsq : ‖R f‖ ^ 2 ≤ B * ‖f‖ * ‖R f‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact (le_abs_self _).trans (by simpa [R, B, mul_assoc] using hinner)
  change ‖R f‖ ≤ B * ‖f‖
  by_cases hz : ‖R f‖ = 0
  · rw [hz]
    positivity
  have hpos : 0 < ‖R f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hfnonneg : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith

/-- Main operator-level beta-variation estimate: the complete positive-half physical
transfer has a quadratic first-order remainder in operator norm, with derivative
candidate given by minus the summed Wilson cylinder-action insertion operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (gamma : ℝ)
    (hgamma : 0 ≤ gamma) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
        H N hN beta hbeta gamma hgamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma - beta‖ ^ 2 := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
      H N hN beta hbeta gamma hgamma
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2 * ‖gamma - beta‖ ^ 2
  change ‖R‖ ≤ B
  apply ContinuousLinearMap.opNorm_le_bound R (by positivity)
  intro f
  simpa [R, B] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_apply_norm_le
      H N hN beta hbeta gamma hgamma f

end

end MathlibAnalytic
end MGAP4D