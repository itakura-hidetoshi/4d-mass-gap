import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularRealSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Tactic

/-!
# Closed regular Hilbert sector and canonical time-average core

The same-root factorial OS construction now provides a genuine `NNReal` C₀ contraction semigroup
on the canonical zero-time regular sector.  Before introducing its infinitesimal generator we close
two analytic points that are needed for an honest densely-defined Hamiltonian:

* the regular sector is closed in the completed direct-limit Hilbert carrier, hence complete;
* positive-time Cesàro averages form a canonical dense smoothing family inside that same sector.

Closedness is not assumed.  It follows from the rational-time contraction estimate and the defining
zero-time regularity by the standard three-epsilon argument.  The time-average construction then
lives directly in the regular Hilbert sector and uses only the already-proved real C₀ semigroup.

No generator, Hamiltonian, self-adjointness, spectral calculus, or mass-gap statement is introduced
in this file.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology Set
open scoped Interval

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The canonical zero-time regular sector is closed in the completed direct-limit Hilbert carrier.
The proof uses only contractivity of the rational-time operators and zero-time regularity. -/
theorem fixedSlotHilbertDirectLimitRegularSubspace_isClosed
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    IsClosed (P.fixedSlotHilbertDirectLimitRegularSubspace :
      Set P.fixedSlotHilbertDirectLimitCompletion) := by
  rw [← closure_eq_iff_isClosed]
  apply Set.Subset.antisymm
  · intro x hx
    change Tendsto
      (fun q : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q x)
      (𝓝 0) (𝓝 x)
    rw [Metric.tendsto_nhds_nhds]
    intro ε hε
    have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨y, hy, hyx⟩ :=
      Metric.mem_closure_iff.mp hx (ε / 3) hε3
    have hyreg : Tendsto
        (fun q : NNRat => P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q y)
        (𝓝 0) (𝓝 y) := hy
    rw [Metric.tendsto_nhds_nhds] at hyreg
    obtain ⟨δ, hδ, hnear⟩ := hyreg (ε / 3) hε3
    refine ⟨δ, hδ, ?_⟩
    intro q hq
    have hmiddle :
        dist (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q y) y < ε / 3 :=
      hnear hq
    have hleft :
        dist (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q x)
            (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q y) ≤
          dist x y := by
      simpa only [dist_eq_norm, map_sub] using
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le q (x - y)
    have hxy : dist x y < ε / 3 := by
      simpa only [dist_comm] using hyx
    calc
      dist (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q x) x ≤
          dist (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q x)
              (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q y) +
            dist (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q y) y +
            dist y x :=
        dist_triangle4 _ _ _ _
      _ < ε := by
        have hyx' : dist y x < ε / 3 := by
          rw [dist_comm]
          exact hxy
        linarith
  · exact subset_closure

/-- The regular sector is therefore a complete real Hilbert space with the inherited norm and
inner product. -/
noncomputable instance fixedSlotHilbertDirectLimitRegularSubspace_completeSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    CompleteSpace P.fixedSlotHilbertDirectLimitRegularSubspace := by
  exact
    P.fixedSlotHilbertDirectLimitRegularSubspace_isClosed.isComplete.completeSpace_coe

/-- The genuine regular-sector real-time orbit is continuous as a map into the regular sector
itself, not merely after coercion into the ambient completion. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeVector_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Continuous (fun t : NNReal =>
      P.fixedSlotHilbertDirectLimitRegularRealTimeVector t x) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hambient : ContinuousAt
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit x) t :=
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous x).continuous.continuousAt
  rw [Metric.continuousAt_iff] at hambient
  obtain ⟨δ, hδ, hclose⟩ := hambient ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  have h := hclose hs
  change dist
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit x s)
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit x t) < ε
  exact h

/-- Clamp negative real times to zero.  This is used only to write ordinary real interval
integrals; all generator limits below are positive-time limits. -/
noncomputable def fixedSlotHilbertDirectLimitRegularClampedRealOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularRealTimeVector s.toNNReal x

/-- The clamped real orbit is continuous. -/
theorem fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Continuous (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x) := by
  exact
    (P.fixedSlotHilbertDirectLimitRegularRealTimeVector_continuous x).comp
      continuous_real_toNNReal

@[simp]
theorem fixedSlotHilbertDirectLimitRegularClampedRealOrbit_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x 0 = x := by
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  change P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism 0 x = x
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_zero_apply x

@[simp]
theorem fixedSlotHilbertDirectLimitRegularClampedRealOrbit_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ) :
    P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit (x + y) s =
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s +
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit y s := by
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  change P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s.toNNReal (x + y) =
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s.toNNReal x +
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s.toNNReal y
  exact map_add _ x y

@[simp]
theorem fixedSlotHilbertDirectLimitRegularClampedRealOrbit_smul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (c : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ) :
    P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit (c • x) s =
      c • P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s := by
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  change P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s.toNNReal (c • x) =
    c • P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s.toNNReal x
  exact map_smul _ c x

/-- The Bochner primitive of the regular-sector orbit. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimePrimitive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ∫ s in (0 : ℝ)..r, P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s

@[simp]
theorem fixedSlotHilbertDirectLimitRegularTimePrimitive_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimePrimitive x 0 = 0 := by
  simp [fixedSlotHilbertDirectLimitRegularTimePrimitive]

/-- Fundamental theorem of calculus for the regular-sector orbit primitive. -/
theorem fixedSlotHilbertDirectLimitRegularTimePrimitive_hasDerivAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) :
    HasDerivAt (P.fixedSlotHilbertDirectLimitRegularTimePrimitive x)
      (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x r) r := by
  simpa only [fixedSlotHilbertDirectLimitRegularTimePrimitive] using
    ((P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x).integral_hasStrictDerivAt 0 r).hasDerivAt

/-- Unnormalized positive-time Bochner integral of a regular orbit. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularTimePrimitive x (h : ℝ)

@[simp]
theorem fixedSlotHilbertDirectLimitRegularTimeIntegral_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeIntegral h (x + y) =
      P.fixedSlotHilbertDirectLimitRegularTimeIntegral h x +
        P.fixedSlotHilbertDirectLimitRegularTimeIntegral h y := by
  simpa only [fixedSlotHilbertDirectLimitRegularTimeIntegral,
    fixedSlotHilbertDirectLimitRegularTimePrimitive,
    fixedSlotHilbertDirectLimitRegularClampedRealOrbit_add] using
    intervalIntegral.integral_add
      ((P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x).intervalIntegrable 0 (h : ℝ))
      ((P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous y).intervalIntegrable 0 (h : ℝ))

@[simp]
theorem fixedSlotHilbertDirectLimitRegularTimeIntegral_smul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (c : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeIntegral h (c • x) =
      c • P.fixedSlotHilbertDirectLimitRegularTimeIntegral h x := by
  simp [fixedSlotHilbertDirectLimitRegularTimeIntegral,
    fixedSlotHilbertDirectLimitRegularTimePrimitive]

/-- Positive-time Cesàro average in the regular Hilbert sector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeAverage
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  (h : ℝ)⁻¹ • P.fixedSlotHilbertDirectLimitRegularTimeIntegral h x

/-- Coercion `NNReal → ℝ` preserves the positive right-neighborhood filter at zero. -/
theorem fixedSlotHilbertDirectLimit_nnreal_coe_tendsto_zero_right :
    Tendsto (fun h : NNReal => (h : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
  change Filter.map NNReal.toReal
      (nhdsWithin (0 : NNReal) (Ioi 0)) ≤
    nhdsWithin (0 : ℝ) (Ioi 0)
  rw [NNReal.map_coe_nhdsGT]
  simp only [NNReal.coe_zero]
  exact le_rfl

/-- Positive-width time averages converge strongly to the original regular vector. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverage_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun h : NNReal => P.fixedSlotHilbertDirectLimitRegularTimeAverage h x)
      (nhdsWithin 0 (Ioi 0)) (nhds x) := by
  have hreal :=
    (P.fixedSlotHilbertDirectLimitRegularTimePrimitive_hasDerivAt x 0).tendsto_slope_zero_right
  have hcomp := hreal.comp fixedSlotHilbertDirectLimit_nnreal_coe_tendsto_zero_right
  simpa [fixedSlotHilbertDirectLimitRegularTimeAverage,
    fixedSlotHilbertDirectLimitRegularTimeIntegral,
    fixedSlotHilbertDirectLimitRegularTimePrimitive] using hcomp

/-- Time averages are additive in the initial vector. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularTimeAverage_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverage h (x + y) =
      P.fixedSlotHilbertDirectLimitRegularTimeAverage h x +
        P.fixedSlotHilbertDirectLimitRegularTimeAverage h y := by
  simp [fixedSlotHilbertDirectLimitRegularTimeAverage, smul_add]

/-- Time averages respect real scalar multiplication. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularTimeAverage_smul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (c : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverage h (c • x) =
      c • P.fixedSlotHilbertDirectLimitRegularTimeAverage h x := by
  simp [fixedSlotHilbertDirectLimitRegularTimeAverage, smul_smul, mul_comm]

/-- The time-average smoothing operation is real-linear. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeAverageLinearMap
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →ₗ[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace where
  toFun := P.fixedSlotHilbertDirectLimitRegularTimeAverage h
  map_add' := P.fixedSlotHilbertDirectLimitRegularTimeAverage_add h
  map_smul' := P.fixedSlotHilbertDirectLimitRegularTimeAverage_smul h

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
