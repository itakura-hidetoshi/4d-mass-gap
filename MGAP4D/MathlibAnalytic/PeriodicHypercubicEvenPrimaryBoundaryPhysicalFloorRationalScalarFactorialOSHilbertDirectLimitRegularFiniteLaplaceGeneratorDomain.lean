import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularYosidaExponentialConvergence
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Finite Laplace resolvent vectors on the same-root regular OS semigroup

This file starts the closed-generator identification package directly from the original regular
factorial-OS `C₀` contraction semigroup.  For a real parameter `lambda` and finite Euclidean time
`h`, we construct the weighted orbit integral

`R_{lambda,h} x = ∫₀ʰ exp (-lambda s) T_s x ds`

and prove, without introducing a new semigroup abstraction, that it lies in the actual right
infinitesimal-generator domain.  Its generator and Hamiltonian values satisfy the exact finite-time
resolvent formula

`A R_{lambda,h} x = lambda R_{lambda,h} x + exp (-lambda h) T_h x - x`,

`H R_{lambda,h} x = x - lambda R_{lambda,h} x - exp (-lambda h) T_h x`.

For positive `lambda`, the terminal term is controlled by contraction and exponential decay.  These
identities are the same-root finite-time input for identifying the infinite semigroup Laplace
resolvent with the already-constructed positive resolvent `(lambda I + H̄)⁻¹`.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace Interval LinearPMap

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

/-- Exponentially weighted original regular OS orbit, clamped only on negative real times. -/
noncomputable def fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  Real.exp ((-lambda) * s) • P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s

/-- Weighted regular OS orbits are continuous on the real line. -/
theorem fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Continuous (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x) := by
  have hscalar : Continuous (fun s : ℝ => Real.exp ((-lambda) * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hscalar.smul (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x)

/-- Weighted regular OS orbits are Bochner integrable on every compact interval. -/
theorem fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (a b : ℝ) :
    IntervalIntegrable
      (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x)
      MeasureTheory.volume a b :=
  (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_continuous lambda x).intervalIntegrable
    a b

@[simp]
theorem fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x 0 = x := by
  simp [fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit,
    fixedSlotHilbertDirectLimitRegularClampedRealOrbit]

/-- Bochner primitive of the exponentially weighted regular OS orbit. -/
noncomputable def fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ∫ s in (0 : ℝ)..r,
    P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s

@[simp]
theorem fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x 0 = 0 := by
  simp [fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive]

/-- The weighted orbit is the derivative of its Bochner primitive. -/
theorem fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_hasDerivAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) :
    HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x)
      (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x r)
      r := by
  simpa only [fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive] using
    ((P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_continuous lambda x)
      .integral_hasStrictDerivAt 0 r).hasDerivAt

/-- Finite-time Laplace integral of the original regular OS orbit. -/
noncomputable def fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x (h : ℝ)

@[simp]
theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_zero_width
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda 0 x = 0 := by
  simp [fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral]

/-- Exponentially renormalized moving-interval primitive obtained by applying the semigroup to a
finite Laplace integral. -/
noncomputable def fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  Real.exp (lambda * r) •
    (P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x ((h : ℝ) + r) -
      P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x r)

@[simp]
theorem fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x 0 =
      P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x := by
  simp [fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive,
    fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral]

/-- Scalar exponential prefactor derivative at zero. -/
theorem fixedSlotHilbertDirectLimitRegularExponentialPrefactor_hasDerivAt_zero
    (lambda : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (lambda * r)) lambda 0 := by
  have hlinear : HasDerivAt (fun r : ℝ => lambda * r) lambda 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_mul lambda
  simpa using hlinear.exp

/-- Moving weighted interval derivative at zero. -/
theorem fixedSlotHilbertDirectLimitRegularExponentialMovingInterval_hasDerivAt_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    HasDerivAt
      (fun r : ℝ =>
        P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x ((h : ℝ) + r) -
          P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x r)
      (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x (h : ℝ) - x)
      0 := by
  have harg : HasDerivAt (fun r : ℝ => (h : ℝ) + r) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (h : ℝ)
  have hshift :
      HasDerivAt
        (fun r : ℝ =>
          P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x ((h : ℝ) + r))
        (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x (h : ℝ))
        0 := by
    have hout :=
      P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_hasDerivAt
        lambda x ((h : ℝ) + 0)
    have hcomp := hout.scomp 0 harg
    simpa using hcomp
  have hzero :
      HasDerivAt
        (P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive lambda x)
        x 0 := by
    simpa using P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_hasDerivAt lambda x 0
  exact hshift.sub hzero

/-- Derivative at zero of the shifted exponential primitive, written in completed original-semigroup
notation. -/
theorem fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_hasDerivAt_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    HasDerivAt
      (P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x)
      (lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x)
      0 := by
  have hscalar := fixedSlotHilbertDirectLimitRegularExponentialPrefactor_hasDerivAt_zero lambda
  have hinterval :=
    P.fixedSlotHilbertDirectLimitRegularExponentialMovingInterval_hasDerivAt_zero lambda h x
  have hproduct := hscalar.smul hinterval
  convert hproduct using 1
  · simp only [fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive]
  · simp only [fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral, mul_zero, Real.exp_zero,
      one_smul, add_zero, P.fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive_zero,
      sub_zero]
    rw [fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit]
    have hh : (h : ℝ).toNNReal = h := by
      exact NNReal.eq (by simp)
    rw [fixedSlotHilbertDirectLimitRegularClampedRealOrbit, hh]
    module

/-- Applying the original OS semigroup to a weighted orbit shifts its real-time argument and produces
the compensating exponential factor. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_exponentiallyWeightedOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ)
    (hs : 0 ≤ s) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s) =
      Real.exp (lambda * (t : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
          (s + (t : ℝ)) := by
  calc
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s) =
      Real.exp ((-lambda) * s) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s) := by
      simp [fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit, map_smul]
    _ = Real.exp ((-lambda) * s) •
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) s := by
      rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_clampedRealOrbit]
    _ = Real.exp ((-lambda) * s) •
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x (s + (t : ℝ)) := by
      rw [P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_endomorphism_eq_add_of_nonneg
        t x s hs]
    _ = Real.exp (lambda * (t : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
          (s + (t : ℝ)) := by
      rw [fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit, smul_smul]
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring

/-- Applying the original regular OS semigroup to a finite Laplace integral gives the shifted
exponential primitive. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x) =
      P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x (t : ℝ) := by
  unfold fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral
  unfold fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t)
    (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
      lambda x 0 (h : ℝ))]
  calc
    (∫ s in (0 : ℝ)..(h : ℝ),
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s)) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        Real.exp (lambda * (t : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
            (s + (t : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hh : (0 : ℝ) ≤ (h : ℝ) := h.coe_nonneg
      rw [uIcc_of_le hh] at hs
      exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_exponentiallyWeightedOrbit
        lambda t x s hs.1
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (0 : ℝ)..(h : ℝ),
          P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x
            (s + (t : ℝ))) := by
      rw [intervalIntegral.integral_smul]
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ),
          P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit lambda x s) := by
      rw [intervalIntegral.integral_comp_add_right]
      simp
    _ = P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x (t : ℝ) := by
      unfold fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive
      unfold fixedSlotHilbertDirectLimitRegularExponentialTimePrimitive
      congr 1
      symm
      simpa [add_comm] using
        intervalIntegral.integral_interval_sub_left
          (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
            lambda x 0 ((t : ℝ) + (h : ℝ)))
          (P.fixedSlotHilbertDirectLimitRegularExponentiallyWeightedOrbit_intervalIntegrable
            lambda x 0 (t : ℝ))

/-- Right difference quotient of a finite Laplace vector is the slope of its shifted primitive. -/
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x) t =
      (t : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x (t : ℝ) -
          P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive lambda h x 0) := by
  unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_finiteLaplaceIntegral]
  rw [P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_zero]

/-- Every finite Laplace integral has the exact expected right-generator value. -/
theorem fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
      (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x)
      (lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x) := by
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hreal :=
    (P.fixedSlotHilbertDirectLimitRegularShiftedExponentialTimePrimitive_hasDerivAt_zero
      lambda h x).tendsto_slope_zero_right
  have hcomp := hreal.comp nnreal_coe_tendsto_zero_right
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_finiteLaplaceIntegral,
    zero_add] using hcomp

/-- Every finite Laplace vector lies in the actual right-generator domain of the original regular OS
semigroup. -/
theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_mem_rightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
      Real.exp ((-lambda) * (h : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x,
    P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_finiteLaplaceIntegral lambda h x⟩

/-- Finite Laplace vector bundled in the actual original right-generator domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x,
    P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_mem_rightGeneratorDomain lambda h x⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x :=
  rfl

/-- Exact finite-time generator resolvent formula. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x) =
      lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x +
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x := by
  apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x))
  exact P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_finiteLaplaceIntegral lambda h x

/-- Exact finite-time Hamiltonian resolvent formula. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_finiteLaplaceIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x) =
      x - lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x -
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply]
  rw [P.fixedSlotHilbertDirectLimitRegularRightGenerator_finiteLaplaceIntegral]
  module

/-- The exponentially decaying terminal orbit is bounded by the scalar weight times the initial
norm. -/
theorem fixedSlotHilbertDirectLimitRegularExponentialTerminal_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖Real.exp ((-lambda) * (h : ℝ)) •
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x‖ ≤
      Real.exp ((-lambda) * (h : ℝ)) * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos ((-lambda) * (h : ℝ)))]
  exact mul_le_mul_of_nonneg_left
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le h x)
    (Real.exp_pos ((-lambda) * (h : ℝ))).le

/-- Collected finite-Laplace generator-domain package. -/
theorem fixedSlotHilbertDirectLimitRegularFiniteLaplaceGeneratorDomain_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) ∧
    (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegralGeneratorDomain lambda h x) =
      x - lambda • P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral lambda h x -
        Real.exp ((-lambda) * (h : ℝ)) •
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularFiniteLaplaceIntegral_mem_rightGeneratorDomain
      lambda h x,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_finiteLaplaceIntegral lambda h x⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
