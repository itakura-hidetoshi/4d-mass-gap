import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRowMassDeficitBoundV5_PZ37AOO
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOQ — Original SU(2) Wilson row mass deficit and global action budget

Diagnostic Lean candidate only. The true original one-slab Wilson kernel is
integrated against the actual normalized spatial Haar measure. The already
verified global action budget gives a pointwise lower bound on the kernel.
Combining this bound with the elementary convexity inequality exp(-x) >= 1-x
yields an H-dependent upper bound on the literal row mass deficit.

Neither this statement nor the global action budget provides an H-uniform
vanishing rate as beta approaches zero while H moves, a fixed positive-coupling
physical spectral gap, or a continuum 4D Yang--Mills mass-gap theorem.
No source promotion before direct Lean, actual MCP, independent PR CI, and
separate postmerge CI.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ

local instance p4Q2PZ37AOQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AOQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AOQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AOQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AOQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AOQ_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37AOQ_fixedLeftKernel_continuous
    (H : ℕ) (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hPair : Continuous (fun B : Cfg => (A, B)) :=
    (continuous_const : Continuous (fun _ : Cfg => A)).prodMk
      (continuous_id : Continuous (fun B : Cfg => B))
  change Continuous
    ((fun p : Cfg × Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta p.1 p.2) ∘ (fun B : Cfg => (A, B)))
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
    H 2 beta).comp hPair

/-- Original finite-volume Wilson kernel's Haar row-mass deficit is bounded by
beta times the genuine original global one-slab action budget. The latter
depends on H; no H-uniform error rate is claimed. -/
theorem p4Q2PZ37AOQ_originalWilsonRowMassDeficit_le_globalBudgetBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    1 -
      (∫ B,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta A B
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) ≤
      beta * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let kernel : Cfg → ℝ := fun B =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta A B
  let C : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let floor : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  haveI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hKernelCont : Continuous kernel :=
    p4Q2PZ37AOQ_fixedLeftKernel_continuous H beta A
  have hKernelInt : Integrable kernel mu :=
    hKernelCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (B : Cfg) : floor ≤ kernel B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
      H 2 (by norm_num) beta hbeta A B
  have hFloorInt : (∫ _ : Cfg, floor ∂mu) = floor := by
    exact integral_eq_const (Filter.Eventually.of_forall fun _ => rfl)
  have hZfloor : floor ≤ (∫ B : Cfg, kernel B ∂mu) := by
    calc
      floor = (∫ _ : Cfg, floor ∂mu) := hFloorInt.symm
      _ ≤ (∫ B : Cfg, kernel B ∂mu) := by
        apply integral_mono_ae (integrable_const floor) hKernelInt
        filter_upwards [] with B
        exact hPoint B
  have hExpLower : 1 - beta * C ≤ floor := by
    change 1 - beta * C ≤ Real.exp (-(beta * C))
    have h := Real.add_one_le_exp (-(beta * C))
    linarith only [h]
  change 1 - (∫ B : Cfg, kernel B ∂mu) ≤ beta * C
  linarith only [hZfloor, hExpLower]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOQ_originalWilsonRowMassDeficit_le_globalBudgetBeta
