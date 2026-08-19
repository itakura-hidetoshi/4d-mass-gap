import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularTimeAverage
import Mathlib.Tactic

/-!
# Same-root infinitesimal generator and OS Hamiltonian on the regular Hilbert sector

This file introduces the infinitesimal generator only after the genuine real-time C₀ contraction
semigroup has been constructed on the canonical factorial OS regular Hilbert sector.

The construction is entirely same-root:

* the right generator is defined by the strong positive-time difference quotient;
* positive-time Cesàro averages lie in its domain and approximate every regular vector, proving
  that the domain is dense;
* the already-proved OS symmetry of every finite-time operator passes to the generator;
* contractivity makes the generator dissipative, hence the Euclidean Hamiltonian `H = -A` has a
  nonnegative quadratic form;
* the domain is invariant under the semigroup and the generator commutes with time evolution;
* the symmetric nonnegative Hamiltonian is sequentially closable.

No self-adjoint closure, spectral theorem, exponential functional calculus, or mass-gap transfer is
claimed here.  Those require the subsequent resolvent/closed-operator package.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology Set
open scoped InnerProductSpace

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

/-- Positive-time right difference quotient of the canonical regular-sector C₀ semigroup. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  (t : ℝ)⁻¹ •
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x - x)

/-- A vector has right generator value `eta` when its strong difference quotient tends to `eta`
from positive times. -/
def FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x eta : P.fixedSlotHilbertDirectLimitRegularSubspace) : Prop :=
  Tendsto
    (fun t : NNReal => P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t)
    (nhdsWithin 0 (Ioi 0)) (nhds eta)

/-- Right generator values are unique. -/
theorem fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x eta zeta : P.fixedSlotHilbertDirectLimitRegularSubspace}
    (heta : P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue x eta)
    (hzeta : P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue x zeta) :
    eta = zeta :=
  tendsto_nhds_unique heta hzeta

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient 0 t = 0 := by
  simp [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient]

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient (x + y) t =
      P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t +
        P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient y t := by
  simp only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient, map_add]
  module

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_smul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (c : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient (c • x) t =
      c • P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t := by
  simp only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient, map_smul]
  module

/-- Zero has generator value zero. -/
theorem fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue 0 0 := by
  simpa only [FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue,
    fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_zero] using
    (tendsto_const_nhds : Tendsto
      (fun _ : NNReal => (0 : P.fixedSlotHilbertDirectLimitRegularSubspace))
      (nhdsWithin 0 (Ioi 0)) (nhds 0))

/-- Generator values are additive. -/
theorem FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue.add
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x y eta zeta : P.fixedSlotHilbertDirectLimitRegularSubspace}
    (heta : P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue x eta)
    (hzeta : P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue y zeta) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue (x + y) (eta + zeta) := by
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at heta hzeta ⊢
  simpa only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_add] using
    heta.add hzeta

/-- Generator values respect real scalar multiplication. -/
theorem FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue.smul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x eta : P.fixedSlotHilbertDirectLimitRegularSubspace}
    (c : ℝ)
    (heta : P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue x eta) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue (c • x) (c • eta) := by
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at heta ⊢
  simpa only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_smul] using
    (tendsto_const_nhds.smul heta : Tendsto
      (fun t : NNReal => c • P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t)
      (nhdsWithin 0 (Ioi 0)) (nhds (c • eta)))

/-- Canonical right-generator domain of the same-root regular C₀ semigroup. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Submodule ℝ P.fixedSlotHilbertDirectLimitRegularSubspace where
  carrier := {x | ∃ eta, P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue x eta}
  zero_mem' := ⟨0, P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_zero⟩
  add_mem' := by
    rintro x y ⟨eta, heta⟩ ⟨zeta, hzeta⟩
    exact ⟨eta + zeta, heta.add P hzeta⟩
  smul_mem' := by
    rintro c x ⟨eta, heta⟩
    exact ⟨c • eta, heta.smul P c⟩

/-- Canonical infinitesimal generator selected on its right-generator domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRightGenerator
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain →ₗ[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace where
  toFun x := Classical.choose x.property
  map_add' := by
    intro x y
    apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
      (Classical.choose_spec (x + y).property)
    exact (Classical.choose_spec x.property).add P (Classical.choose_spec y.property)
  map_smul' := by
    intro c x
    apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
      (Classical.choose_spec (c • x).property)
    exact (Classical.choose_spec x.property).smul P c

/-- The selected generator has its defining strong right-limit value. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue x
      (P.fixedSlotHilbertDirectLimitRegularRightGenerator x) :=
  Classical.choose_spec x.property

/-- Euclidean OS Hamiltonian on the same domain, with the convention `H = -A`. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRightHamiltonian
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain →ₗ[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  -P.fixedSlotHilbertDirectLimitRegularRightGenerator

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x =
      -P.fixedSlotHilbertDirectLimitRegularRightGenerator x :=
  rfl

/-- Evolving an already evolved vector at a nonnegative real time adds the times inside the
clamped real orbit. -/
theorem fixedSlotHilbertDirectLimitRegularClampedRealOrbit_endomorphism_eq_add_of_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ) (hs : 0 ≤ s) :
    P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) s =
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x (s + (t : ℝ)) := by
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  have hs_to : s.toNNReal = NNReal.mk s hs := Real.toNNReal_of_nonneg hs
  have hsum : (s + (t : ℝ)).toNNReal = NNReal.mk s hs + t := by
    apply NNReal.eq
    simp [Real.coe_toNNReal, add_nonneg hs t.coe_nonneg]
  rw [hs_to, hsum]
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply _ _ x

/-- Time evolution commutes pointwise with the clamped real orbit. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_clampedRealOrbit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (s : ℝ) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s) =
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) s := by
  unfold fixedSlotHilbertDirectLimitRegularClampedRealOrbit
  calc
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularRealTimeVector s.toNNReal x) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (t + s.toNNReal) x :=
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply t s.toNNReal x
    _ = P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism (s.toNNReal + t) x := by
      rw [add_comm]
    _ = P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s.toNNReal
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) :=
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply s.toNNReal t x).symm

/-- Time evolution commutes with the regular-sector time integral. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_timeIntegral
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularTimeIntegral h x) =
      P.fixedSlotHilbertDirectLimitRegularTimeIntegral h
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) := by
  unfold fixedSlotHilbertDirectLimitRegularTimeIntegral
  unfold fixedSlotHilbertDirectLimitRegularTimePrimitive
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t)
    ((P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x)
      .intervalIntegrable 0 (h : ℝ))]
  apply intervalIntegral.integral_congr
  intro s hs
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_clampedRealOrbit t x s

/-- Evolution of the unnormalized average is the difference of two primitive values. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_timeIntegral_eq_primitive_sub
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularTimeIntegral h x) =
      P.fixedSlotHilbertDirectLimitRegularTimePrimitive x ((h : ℝ) + (t : ℝ)) -
        P.fixedSlotHilbertDirectLimitRegularTimePrimitive x (t : ℝ) := by
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_timeIntegral]
  unfold fixedSlotHilbertDirectLimitRegularTimeIntegral
  unfold fixedSlotHilbertDirectLimitRegularTimePrimitive
  calc
    (∫ s in (0 : ℝ)..(h : ℝ),
      P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) s) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x (s + (t : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hh : (0 : ℝ) ≤ (h : ℝ) := h.coe_nonneg
      rw [uIcc_of_le hh] at hs
      exact P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_endomorphism_eq_add_of_nonneg
        t x s hs.1
    _ = ∫ s in (0 : ℝ) + (t : ℝ)..(h : ℝ) + (t : ℝ),
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s := by
      rw [intervalIntegral.integral_comp_add_right]
    _ = ∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ),
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s := by simp
    _ = (∫ s in (0 : ℝ)..((h : ℝ) + (t : ℝ)),
        P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s) -
        ∫ s in (0 : ℝ)..(t : ℝ),
          P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x s := by
      symm
      simpa [add_comm] using
        intervalIntegral.integral_interval_sub_left
          ((P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x)
            .intervalIntegrable 0 ((t : ℝ) + (h : ℝ)))
          ((P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x)
            .intervalIntegrable 0 (t : ℝ))

/-- Moving interval primitive used to identify the generator of a time average. -/
noncomputable def fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularTimePrimitive x ((h : ℝ) + r) -
    P.fixedSlotHilbertDirectLimitRegularTimePrimitive x r

/-- Derivative of the moving interval primitive at zero. -/
theorem fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive_hasDerivAt_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    HasDerivAt (P.fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive h x)
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x) 0 := by
  have harg : HasDerivAt (fun r : ℝ => (h : ℝ) + r) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (h : ℝ)
  have hshift : HasDerivAt
      (fun r : ℝ => P.fixedSlotHilbertDirectLimitRegularTimePrimitive x ((h : ℝ) + r))
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x) 0 := by
    have hout := P.fixedSlotHilbertDirectLimitRegularTimePrimitive_hasDerivAt x ((h : ℝ) + 0)
    have hcomp := hout.scomp 0 harg
    simpa [fixedSlotHilbertDirectLimitRegularClampedRealOrbit] using hcomp
  have hzero : HasDerivAt (P.fixedSlotHilbertDirectLimitRegularTimePrimitive x) x 0 := by
    simpa using P.fixedSlotHilbertDirectLimitRegularTimePrimitive_hasDerivAt x 0
  simpa [fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive] using hshift.sub hzero

/-- Difference quotient of a time average is the normalized slope of the moving interval
primitive. -/
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_timeAverage
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
        (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x) t =
      (h : ℝ)⁻¹ •
        ((t : ℝ)⁻¹ •
          (P.fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive h x (t : ℝ) -
            P.fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive h x 0)) := by
  simp only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient,
    fixedSlotHilbertDirectLimitRegularTimeAverage, map_smul]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_timeIntegral_eq_primitive_sub]
  simp only [fixedSlotHilbertDirectLimitRegularTimeIntegral,
    fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive, add_zero,
    fixedSlotHilbertDirectLimitRegularTimePrimitive_zero, sub_zero]
  module

/-- Every fixed-width time average has the expected right generator value. -/
theorem fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_timeAverage
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
      (P.fixedSlotHilbertDirectLimitRegularTimeAverage h x)
      ((h : ℝ)⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x)) := by
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hreal :=
    (P.fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive_hasDerivAt_zero h x)
      .tendsto_slope_zero_right
  have hscaled := (tendsto_const_nhds.smul hreal : Tendsto
    (fun r : ℝ => (h : ℝ)⁻¹ •
      (r⁻¹ •
        (P.fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive h x (0 + r) -
          P.fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive h x 0)))
    (nhdsWithin 0 (Ioi 0))
    (nhds ((h : ℝ)⁻¹ •
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x))))
  have hcomp := hscaled.comp fixedSlotHilbertDirectLimit_nnreal_coe_tendsto_zero_right
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_timeAverage,
    zero_add] using hcomp

/-- Every time average lies in the right-generator domain. -/
theorem fixedSlotHilbertDirectLimitRegularTimeAverage_mem_rightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularTimeAverage h x ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨(h : ℝ)⁻¹ • (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism h x - x),
    P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_timeAverage h x⟩

/-- The canonical generator/Hamiltonian domain is dense in the regular Hilbert sector. -/
theorem fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_dense
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Dense (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :
      Set P.fixedSlotHilbertDirectLimitRegularSubspace) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  apply mem_closure_of_tendsto
    (P.fixedSlotHilbertDirectLimitRegularTimeAverage_tendsto_zero x)
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact P.fixedSlotHilbertDirectLimitRegularTimeAverage_mem_rightGeneratorDomain h x

/-- Finite-time OS symmetry holds already at the level of right difference quotients. -/
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t) y =
      inner ℝ x (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient y t) := by
  simp only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient,
    real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_symmetric t x y]

/-- The infinitesimal generator is symmetric on its canonical dense domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator x)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      inner ℝ (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator y) := by
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  have hy := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue y
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx hy
  have hleft := hx.inner (tendsto_const_nhds : Tendsto
    (fun _ : NNReal => (y : P.fixedSlotHilbertDirectLimitRegularSubspace))
    (nhdsWithin 0 (Ioi 0)) (nhds y))
  have hright := (tendsto_const_nhds : Tendsto
    (fun _ : NNReal => (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
    (nhdsWithin 0 (Ioi 0)) (nhds x)).inner hy
  have hfun :
      (fun t : NNReal => inner ℝ
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) t)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace)) =
      (fun t : NNReal => inner ℝ
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
          (y : P.fixedSlotHilbertDirectLimitRegularSubspace) t)) := by
    funext t
    exact P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_symmetric t x y
  rw [hfun] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The OS Hamiltonian `H=-A` is symmetric on the same dense domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_symmetric
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x y : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
        (y : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      inner ℝ (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian y) := by
  simp only [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply,
    inner_neg_left, inner_neg_right]
  exact congrArg Neg.neg
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_inner_symmetric x y)

/-- A contraction cannot increase its pairing with the initial vector. -/
theorem fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_le_self
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) x ≤
      inner ℝ x x := by
  calc
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) x ≤
        ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x‖ * ‖x‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le t x)
        (norm_nonneg x)
    _ = inner ℝ x x := (real_inner_self_eq_norm_mul_norm x).symm

/-- Positive-time generator quotients are dissipative. -/
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_nonpos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) (ht : 0 < t) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t) x ≤ 0 := by
  have hsub :
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x - x) x ≤ 0 := by
    rw [inner_sub_left]
    exact sub_nonpos.mpr
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_inner_le_self t x)
  have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
  have hinv : 0 ≤ (t : ℝ)⁻¹ := inv_nonneg.mpr htReal.le
  have hmul := mul_nonpos_of_nonneg_of_nonpos hinv hsub
  simpa [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient,
    real_inner_smul_left] using hmul

/-- The canonical generator is dissipative. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_inner_nonpos
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator x)
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace) ≤ 0 := by
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx
  have hinner := hx.inner (tendsto_const_nhds : Tendsto
    (fun _ : NNReal => (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
    (nhdsWithin 0 (Ioi 0)) (nhds x))
  apply le_of_tendsto_of_tendsto hinner tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_inner_nonpos x t ht

/-- The same-root OS Hamiltonian has nonnegative quadratic form on its dense domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    0 ≤ inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply, inner_neg_left]
  exact neg_nonneg.mpr
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_inner_nonpos x)

/-- Difference quotients commute with real-time evolution. -/
theorem fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_endomorphism
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x) t =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t) := by
  simp only [fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient, map_smul, map_sub]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply t s x]
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply s t x]
  rw [add_comm t s]

/-- Every real-time operator preserves the generator domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) ∈
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain := by
  refine ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
      (P.fixedSlotHilbertDirectLimitRegularRightGenerator x), ?_⟩
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx
  have hmap :=
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s).continuous.continuousAt.tendsto.comp hx
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_endomorphism] using hmap

/-- The generator commutes with the C₀ semigroup on its invariant domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_endomorphism
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightGenerator
        ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x,
          P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant s x⟩ =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (P.fixedSlotHilbertDirectLimitRegularRightGenerator x) := by
  apply P.fixedSlotHilbertDirectLimitRegularHasRightGeneratorValue_unique
    (P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x,
        P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant s x⟩)
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
  have hx := P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue x
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hx
  have hmap :=
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s).continuous.continuousAt.tendsto.comp hx
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient_endomorphism] using hmap

/-- The Hamiltonian likewise commutes with the C₀ semigroup on its invariant domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_endomorphism
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s x,
          P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant s x⟩ =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism s
        (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x) := by
  simp only [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply, map_neg]
  rw [P.fixedSlotHilbertDirectLimitRegularRightGenerator_endomorphism]

/-- Sequential closability of the same-root right generator. -/
theorem fixedSlotHilbertDirectLimitRegularRightGenerator_sequentially_closable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : ℕ → P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain}
    {eta : P.fixedSlotHilbertDirectLimitRegularSubspace}
    (hx : Tendsto
      (fun n => (x n : P.fixedSlotHilbertDirectLimitRegularSubspace)) atTop (nhds 0))
    (hgenerator : Tendsto
      (fun n => P.fixedSlotHilbertDirectLimitRegularRightGenerator (x n)) atTop (nhds eta)) :
    eta = 0 := by
  have horthogonal : ∀ z : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain,
      inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) = 0 := by
    intro z
    have hperturbation (r : ℝ) :
        inner ℝ
          (eta + r • P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
          (r • (z : P.fixedSlotHilbertDirectLimitRegularSubspace)) ≤ 0 := by
      have hleft : Tendsto
          (fun n => P.fixedSlotHilbertDirectLimitRegularRightGenerator (x n + r • z))
          atTop
          (nhds (eta + r • P.fixedSlotHilbertDirectLimitRegularRightGenerator z)) := by
        have hconst : Tendsto
            (fun _ : ℕ => r • P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
            atTop (nhds (r • P.fixedSlotHilbertDirectLimitRegularRightGenerator z)) :=
          tendsto_const_nhds
        simpa using hgenerator.add hconst
      have hright : Tendsto
          (fun n => ((x n + r • z : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
            P.fixedSlotHilbertDirectLimitRegularSubspace))
          atTop (nhds (r • (z : P.fixedSlotHilbertDirectLimitRegularSubspace))) := by
        have hconst : Tendsto
            (fun _ : ℕ => r • (z : P.fixedSlotHilbertDirectLimitRegularSubspace))
            atTop (nhds (r • (z : P.fixedSlotHilbertDirectLimitRegularSubspace))) :=
          tendsto_const_nhds
        simpa using hx.add hconst
      have hinner := hleft.inner hright
      apply le_of_tendsto_of_tendsto hinner tendsto_const_nhds
      exact Filter.Eventually.of_forall fun n =>
        P.fixedSlotHilbertDirectLimitRegularRightGenerator_inner_nonpos (x n + r • z)
    have hquadratic (r : ℝ) :
        r * inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) +
          r ^ 2 * inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
            (z : P.fixedSlotHilbertDirectLimitRegularSubspace) ≤ 0 := by
      have h := hperturbation r
      simpa [inner_add_left, real_inner_smul_left, real_inner_smul_right,
        pow_two, mul_assoc] using h
    have hq : inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
        (z : P.fixedSlotHilbertDirectLimitRegularSubspace) ≤ 0 :=
      P.fixedSlotHilbertDirectLimitRegularRightGenerator_inner_nonpos z
    by_contra hnonzero
    have hsquare : 0 < inner ℝ eta
        (z : P.fixedSlotHilbertDirectLimitRegularSubspace) ^ 2 :=
      sq_pos_of_ne_zero hnonzero
    have hden : 0 < 1 - inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
        (z : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
      linarith
    have hchosen := hquadratic
      (inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) /
        (1 - inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
          (z : P.fixedSlotHilbertDirectLimitRegularSubspace)))
    have hidentity :
        (inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) /
              (1 - inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
                (z : P.fixedSlotHilbertDirectLimitRegularSubspace))) *
            inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) +
          (inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) /
              (1 - inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
                (z : P.fixedSlotHilbertDirectLimitRegularSubspace))) ^ 2 *
            inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
              (z : P.fixedSlotHilbertDirectLimitRegularSubspace) =
          inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) ^ 2 /
            (1 - inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
              (z : P.fixedSlotHilbertDirectLimitRegularSubspace)) ^ 2 := by
      field_simp [ne_of_gt hden]
      <;> ring
    rw [hidentity] at hchosen
    have hpositive : 0 <
        inner ℝ eta (z : P.fixedSlotHilbertDirectLimitRegularSubspace) ^ 2 /
          (1 - inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightGenerator z)
            (z : P.fixedSlotHilbertDirectLimitRegularSubspace)) ^ 2 :=
      div_pos hsquare (sq_pos_of_pos hden)
    exact (not_lt_of_ge hchosen) hpositive
  have hclosed : IsClosed {z : P.fixedSlotHilbertDirectLimitRegularSubspace |
      inner ℝ eta z = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsubset :
      (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :
        Set P.fixedSlotHilbertDirectLimitRegularSubspace) ⊆
      {z : P.fixedSlotHilbertDirectLimitRegularSubspace | inner ℝ eta z = 0} := by
    intro z hz
    exact horthogonal ⟨z, hz⟩
  have hetaClosure : eta ∈ closure
      (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :
        Set P.fixedSlotHilbertDirectLimitRegularSubspace) := by
    rw [P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_dense.closure_eq]
    exact mem_univ eta
  have hetaInner : inner ℝ eta eta = 0 :=
    (closure_minimal hsubset hclosed) hetaClosure
  have hnormSq : ‖eta‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hetaInner
  have hnorm : ‖eta‖ = 0 := by
    nlinarith [norm_nonneg eta]
  exact norm_eq_zero.mp hnorm

/-- Sequential closability of the symmetric nonnegative OS Hamiltonian. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_sequentially_closable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : ℕ → P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain}
    {eta : P.fixedSlotHilbertDirectLimitRegularSubspace}
    (hx : Tendsto
      (fun n => (x n : P.fixedSlotHilbertDirectLimitRegularSubspace)) atTop (nhds 0))
    (hHamiltonian : Tendsto
      (fun n => P.fixedSlotHilbertDirectLimitRegularRightHamiltonian (x n)) atTop (nhds eta)) :
    eta = 0 := by
  have hgenerator : Tendsto
      (fun n => P.fixedSlotHilbertDirectLimitRegularRightGenerator (x n))
      atTop (nhds (-eta)) := by
    simpa [P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply] using hHamiltonian.neg
  have hzero : -eta = 0 :=
    P.fixedSlotHilbertDirectLimitRegularRightGenerator_sequentially_closable hx hgenerator
  exact neg_eq_zero.mp hzero

/-- Collected mathematical status of the canonical same-root OS Hamiltonian core: dense domain,
symmetry, and nonnegative quadratic form. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_dense_symmetric_nonnegative
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Dense (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :
      Set P.fixedSlotHilbertDirectLimitRegularSubspace) ∧
    (∀ x y : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain,
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
          (y : P.fixedSlotHilbertDirectLimitRegularSubspace) =
        inner ℝ (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
          (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian y)) ∧
    (∀ x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain,
      0 ≤ inner ℝ (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_dense,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_symmetric,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_inner_nonneg⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
