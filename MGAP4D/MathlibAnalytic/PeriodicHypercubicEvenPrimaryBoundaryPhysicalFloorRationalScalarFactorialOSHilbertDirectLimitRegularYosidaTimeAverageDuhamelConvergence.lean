import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularYosidaOrbitGeneratorConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Duhamel convergence of Yosida exponentials on the canonical dense time-average core

The same-root regular OS semigroup already supplies a canonical dense smoothing core: positive-time
Cesàro averages of regular vectors.  The preceding layer aligns the original generator/Hamiltonian
with the closed Hamiltonian and proves orbitwise convergence of the bounded dyadic Yosida
Hamiltonians, together with a uniform `2 ‖H x‖` domination.

This file turns those ingredients into a genuine semigroup approximation theorem on that dense
core.  The route is entirely same-root:

* write a real-time formula for the orbit of a time-average core vector using the existing Bochner
  primitive;
* differentiate that formula by the fundamental theorem of calculus;
* build the Duhamel path `s ↦ Eₙ(t-s) T_s x`;
* identify its derivative with the Yosida generator error transported by the contraction `Eₙ`;
* bound the endpoint discrepancy by the integral of the generator error;
* apply dominated convergence, using the orbitwise convergence and uniform graph-core bound already
  proved, to obtain convergence uniformly for `0 ≤ t ≤ R` on every fixed compact time interval.

No spectral functional calculus, no abstract semigroup approximation theorem, and no new continuity
or coercivity hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace LinearPMap Interval

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

/-- A positive-time Cesàro average, bundled in the canonical dense right-generator domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularTimeAverage h x,
    P.fixedSlotHilbertDirectLimitRegularTimeAverage_mem_rightGeneratorDomain h x⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularTimeAverage h x :=
  rfl

/-- Exact generator value of the canonical time-average core vector. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_timeAverage
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        (P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x) =
      (h : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x) := by
  apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x))
  exact P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_timeAverage h x

/-- Exact Hamiltonian value of the canonical time-average core vector. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_timeAverage
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x) =
      -((h : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x)) := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply,
    P.fixedSlotHilbertDirectLimitRegularRightGenerator_timeAverage]

/-- Real-line formula for the orbit of a time-average vector.  On nonnegative real times this is
exactly the original OS orbit; unlike the latter it is differentiable on the whole real line because
it is written as a difference of Bochner primitives. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  (h : ℝ)⁻¹ •
    (P.fixedSlotHilbertDirectLimitRegularTimePrimitive x ((h : ℝ) + r) -
      P.fixedSlotHilbertDirectLimitRegularTimePrimitive x r)

/-- Explicit derivative field of the real-line time-average orbit formula. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  (h : ℝ)⁻¹ •
    (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x ((h : ℝ) + r) -
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x r)

/-- The primitive formula is differentiable everywhere with the explicit derivative field above. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_hasDerivAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) :
    HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x)
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative h x r) r := by
  have harg : HasDerivAt (fun s : ℝ => (h : ℝ) + s) 1 r := by
    simpa using (hasDerivAt_id (x := r)).const_add (h : ℝ)
  have hshift :=
    (P.fixedSlotHilbertDirectLimitRegularTimePrimitive_hasDerivAt x ((h : ℝ) + r)).scomp r harg
  have hbase := P.fixedSlotHilbertDirectLimitRegularTimePrimitive_hasDerivAt x r
  have hdiff := hshift.sub hbase
  have hscaled := hdiff.const_smul (h : ℝ)⁻¹
  simpa [fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula,
    fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative,
    Function.comp_def] using hscaled

/-- At every nonnegative real time, the primitive formula is exactly the original OS orbit of the
Cesàro-average core vector. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_eq_clamped
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) (hr : 0 ≤ r) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x r =
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x) r := by
  unfold fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  unfold fixedSlotHilbertDirectLimitRegularTimeAverage
  change
    (h : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularTimePrimitive x ((h : ℝ) + r) -
          P.fixedSlotHilbertDirectLimitRegularTimePrimitive x r) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism r.toNNReal
        ((h : ℝ)⁻¹ • P.fixedSlotHilbertDirectLimitRegularTimeIntegral h x)
  rw [map_smul,
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_timeIntegral_eq_primitive_sub]
  simp [Real.toNNReal_of_nonneg hr]

/-- On nonnegative times, the explicit derivative field is the negative Hamiltonian orbit. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative_eq_neg_hamiltonian_orbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) (hr : 0 ≤ r) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative h x r =
      - P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit
          (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
            (P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x)) r := by
  let t : NNReal := r.toNNReal
  have ht : (t : ℝ) = r := by
    simp [t, Real.toNNReal_of_nonneg hr]
  have hsumNonneg : 0 ≤ (h : ℝ) + r := add_nonneg h.coe_nonneg hr
  have hshift :
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x ((h : ℝ) + r) =
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x) := by
    unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
    have hsum : ((h : ℝ) + r).toNNReal = h + t := by
      apply NNReal.eq
      simp [t, Real.toNNReal_of_nonneg hsumNonneg, Real.toNNReal_of_nonneg hr]
    rw [hsum]
    rw [add_comm h t]
    exact
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply t h x).symm
  have hbase :
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x r =
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x := by
    unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
    rfl
  rw [fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative, hshift, hbase,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_timeAverage]
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  rw [show r.toNNReal = t by rfl]
  change
    (h : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x) -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) =
      - P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (-((h : ℝ)⁻¹ •
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x)))
  rw [map_neg, map_smul, map_sub]
  module

/-- The real-line time-average formula at zero is the actual time-average vector. -/
@[simp]
theorem fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x 0 =
      P.fixedSlotHilbertDirectLimitRegularTimeAverage h x := by
  unfold fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula
  unfold fixedSlotHilbertDirectLimitRegularTimeAverage
  unfold fixedSlotHilbertDirectLimitRegularTimeIntegral
  simp

/-- Generator error along the time-average core orbit, written on the whole real line.  On positive
times it is exactly `Hₙ T_r y - T_r H y`. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x r) +
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative h x r

/-- The generator error is continuous in the real time variable. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Continuous (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x) := by
  have horbit : Continuous
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x) := by
    rw [continuous_iff_continuousAt]
    intro r
    exact
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_hasDerivAt h x r).continuousAt
  have hshift : Continuous (fun r : ℝ =>
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x ((h : ℝ) + r)) :=
    (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x).comp
      (continuous_const.add continuous_id)
  have hbase : Continuous
      (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x) :=
    P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x
  have hderiv : Continuous
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative h x) := by
    unfold fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative
    exact (hshift.sub hbase).const_smul (h : ℝ)⁻¹
  unfold fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError
  exact
    ((P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n).continuous.comp horbit).add hderiv

/-- On nonnegative times, the generator error is uniformly dominated by the original graph norm. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) (hr : 0 ≤ r) :
    ‖P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r‖ ≤
      2 * ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x)‖ := by
  let y := P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x
  have hmain :=
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_timeTranslate_error_norm_le
      n r.toNNReal y
  rw [fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError,
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_eq_clamped h x r hr,
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative_eq_neg_hamiltonian_orbit h x r hr]
  simpa only [fixedSlotHilbertDirectLimitRegularClampedRealOrbit,
    y, P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector_coe,
    sub_eq_add_neg] using hmain

/-- At every nonnegative real time, the generator error tends strongly to zero. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) (hr : 0 ≤ r) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r)
      atTop (nhds 0) := by
  let y := P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x
  let v : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism r.toNNReal
      (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian y)
  have hmain :=
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_timeTranslate
      r.toNNReal y
  have hconst : Tendsto (fun _ : ℕ => v) atTop (nhds v) := tendsto_const_nhds
  have hsub := hmain.sub hconst
  have hv : v - v = (0 : P.fixedSlotHilbertDirectLimitRegularSubspace) := sub_self v
  rw [hv] at hsub
  unfold fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError
  rw [P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_eq_clamped h x r hr,
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative_eq_neg_hamiltonian_orbit h x r hr]
  simpa only [fixedSlotHilbertDirectLimitRegularClampedRealOrbit,
    y, v, P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector_coe,
    sub_eq_add_neg] using hsub

/-- Duhamel interpolation path between `Eₙ(t)y` and `T_t y` for a time-average core vector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n ((t : ℝ) - r)
    (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x r)

/- Exact derivative of the Duhamel path. -/
set_option maxHeartbeats 1000000 in
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath_hasDerivAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) :
    HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath n t h x)
      (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n ((t : ℝ) - r)
        (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r)) r := by
  let E : P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n ((t : ℝ) - r)
  let A : P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian n
  let u : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x r
  let u' : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitDerivative h x r
  have harg : HasDerivAt (fun s : ℝ => (t : ℝ) - s) (-1) r := by
    simpa using (hasDerivAt_const r (t : ℝ)).sub (hasDerivAt_id (x := r))
  have hEraw : HasDerivAt
      (fun s : ℝ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n
        ((t : ℝ) - s))
      ((-1 : ℝ) •
        (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n ((t : ℝ) - r) *
          P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian n)) r := by
    have hOuterF :=
      (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_hasDerivAt
        n ((t : ℝ) - r)).hasFDerivAt
    have hCompF :=
      HasFDerivAt.comp (f := fun s : ℝ => (t : ℝ) - s) r hOuterF harg.hasFDerivAt
    have hComp := hCompF.hasDerivAt
    simpa [Function.comp_def] using hComp
  have hE : HasDerivAt
      (fun s : ℝ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n
        ((t : ℝ) - s))
      ((-1 : ℝ) • (E * A)) r := by
    simpa only [E, A] using hEraw
  have hu : HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula h x) u' r := by
    simpa only [u'] using
      P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_hasDerivAt h x r
  have happly := hE.clm_apply hu
  have hraw : HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath n t h x)
      (((-1 : ℝ) • (E * A)) u + E u') r := by
    simpa only [fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath,
      E, u, u'] using happly
  have hA : A u = - P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n u := by
    simp [A, fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian]
  have hleft : ((-1 : ℝ) • (E * A)) u = - E (A u) := by
    simp
  have halg :
      (((-1 : ℝ) • (E * A)) u + E u') =
        E (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r) := by
    rw [hleft]
    unfold fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError
    rw [map_add, hA, map_neg]
    module
  rw [← halg]
  simpa only [E] using hraw

/-- The real-time bounded Yosida exponential is a contraction at nonnegative real parameters. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_norm_le_of_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (z : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal n r z‖ ≤ ‖z‖ := by
  let t : NNReal := ⟨r, hr⟩
  have ht : (t : ℝ) = r := rfl
  simpa only [fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential, ht] using
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential_norm_le n t z

/-- The Duhamel path starts at the bounded Yosida exponential orbit. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath n t h x 0 =
      P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t
        (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x) := by
  simp [fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath,
    fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential]

/-- The Duhamel path ends at the original OS semigroup orbit. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath_end
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath n t h x (t : ℝ) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x) := by
  rw [fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath]
  simp only [sub_self, P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_zero]
  rw [P.fixedSlotHilbertDirectLimitRegularTimeAverageRealOrbitFormula_eq_clamped h x (t : ℝ)
    t.coe_nonneg]
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  simp

/-- Duhamel endpoint inequality: on the dense time-average core, semigroup discrepancy is bounded by
the integral of the same-root generator error. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamel_norm_le_integral_error
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t
          (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x) -
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x)‖ ≤
      ∫ r in (0 : ℝ)..(t : ℝ),
        ‖P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r‖ := by
  let f := P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath n t h x
  let B : ℝ → ℝ := fun r =>
    ‖P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r‖
  have hdiff : Differentiable ℝ f := by
    intro r
    exact (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath_hasDerivAt n t h x r).differentiableAt
  have hcont : ContinuousOn f (Icc (0 : ℝ) (t : ℝ)) := hdiff.continuous.continuousOn
  have hderiv : ∀ᵐ r, r ∈ Ioo (0 : ℝ) (t : ℝ) → ‖deriv f r‖ ≤ B r := by
    filter_upwards [] with r
    intro hr
    have hformula :=
      P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath_hasDerivAt n t h x r
    rw [hformula.deriv]
    exact P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponentialReal_norm_le_of_nonneg
      n ((t : ℝ) - r) (sub_nonneg.mpr hr.2.le) _
  have hB : IntervalIntegrable B volume (0 : ℝ) (t : ℝ) :=
    (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_continuous n h x).norm.intervalIntegrable
      0 (t : ℝ)
  have hmain := norm_sub_le_integral_of_norm_deriv_le_of_le
    (f := f) (B := B) t.coe_nonneg hcont hdiff.differentiableOn hderiv hB
  dsimp [f, B] at hmain
  rw [P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath_zero,
    P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelPath_end] at hmain
  simpa only [norm_sub_rev] using hmain

/-- For each compact time horizon, the integral of the generator error tends to zero. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_integral_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (R h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        ∫ r in (0 : ℝ)..(R : ℝ),
          ‖P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r‖)
      atTop (nhds 0) := by
  let y := P.fixedSlotHilbertDirectLimitRegularTimeAverageGeneratorCoreVector h x
  let bound : ℝ → ℝ := fun _ =>
    2 * ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian y‖
  let F : ℕ → ℝ → ℝ := fun n r =>
    ‖P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r‖
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (F n) (volume.restrict (Ι (0 : ℝ) (R : ℝ))) := by
    filter_upwards [] with n
    exact (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_continuous n h x).norm.aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ r ∂volume,
      r ∈ Ι (0 : ℝ) (R : ℝ) → ‖F n r‖ ≤ bound r := by
    filter_upwards [] with n
    filter_upwards [] with r
    intro hr
    have hR : (0 : ℝ) ≤ (R : ℝ) := R.coe_nonneg
    rw [uIoc_of_le hR] at hr
    have herr := P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_norm_le
      n h x r hr.1.le
    simpa [F, bound, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), y] using herr
  have hboundInt : IntervalIntegrable bound volume (0 : ℝ) (R : ℝ) := by
    exact intervalIntegrable_const
  have hlim : ∀ᵐ r ∂volume,
      r ∈ Ι (0 : ℝ) (R : ℝ) →
        Tendsto (fun n : ℕ => F n r) atTop (nhds 0) := by
    filter_upwards [] with r
    intro hr
    have hR : (0 : ℝ) ≤ (R : ℝ) := R.coe_nonneg
    rw [uIoc_of_le hR] at hr
    have herr := P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_tendsto_zero
      h x r hr.1.le
    have hnorm := tendsto_norm.comp herr
    simpa [F] using hnorm
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (F := F) (f := fun _ : ℝ => (0 : ℝ))
    (a := (0 : ℝ)) (b := (R : ℝ)) (μ := volume)
    bound hmeas hbound hboundInt hlim
  simpa [F] using hDCT

/-- Compact-time locally uniform Yosida semigroup convergence on every canonical time-average core
vector.  This is expressed directly in epsilon form, avoiding any auxiliary abstract semigroup
wrapper. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaExponential_tendsto_uniformOn_compact
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (R h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t : NNReal, t ≤ R →
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t
            (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x) -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
            (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x)‖ < ε := by
  let B : ℕ → ℝ → ℝ := fun n r =>
    ‖P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError n h x r‖
  have hInt := P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_integral_tendsto_zero
    R h x
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (∫ r in (0 : ℝ)..(R : ℝ), B n r) < ε := by
    exact hInt (Iio_mem_nhds hε)
  filter_upwards [hsmall] with n hn
  intro t ht
  have hduhamel :=
    P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamel_norm_le_integral_error n t h x
  have hBcont : Continuous (B n) :=
    (P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaGeneratorError_continuous n h x).norm
  have hBint : IntervalIntegrable (B n) volume (0 : ℝ) (R : ℝ) :=
    hBcont.intervalIntegrable 0 (R : ℝ)
  have hmono :
      (∫ r in (0 : ℝ)..(t : ℝ), B n r) ≤
        ∫ r in (0 : ℝ)..(R : ℝ), B n r := by
    apply intervalIntegral.integral_mono_interval
      (c := (0 : ℝ)) (d := (R : ℝ))
      (le_refl (0 : ℝ)) t.coe_nonneg
    · exact_mod_cast ht
    · filter_upwards [] with r
      exact norm_nonneg _
    · exact hBint
  exact hduhamel.trans_lt (hmono.trans_lt hn)

/-- Collected dense-core Duhamel convergence package. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverageYosidaDuhamelConvergence_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (∀ R : NNReal, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ t : NNReal, t ≤ R →
        ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t
              (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x) -
            P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
              (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x)‖ < ε) ∧
    (∀ t : NNReal,
      Tendsto
        (fun n : ℕ =>
          P.fixedSlotHilbertDirectLimitRegularDyadicYosidaExponential n t
            (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x))
        atTop
        (nhds (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x)))) := by
  refine ⟨?_, ?_⟩
  · intro R ε hε
    exact P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaExponential_tendsto_uniformOn_compact
      R h x hε
  · intro t
    rw [Metric.tendsto_atTop]
    intro ε hε
    have huni :=
      P.fixedSlotHilbertDirectLimitRegularTimeAverageYosidaExponential_tendsto_uniformOn_compact
        t h x hε
    rcases eventually_atTop.1 huni with ⟨N0, hN0⟩
    refine ⟨N0, ?_⟩
    intro n hn
    have hpoint := hN0 n hn t (le_refl t)
    simpa only [dist_eq_norm] using hpoint

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D