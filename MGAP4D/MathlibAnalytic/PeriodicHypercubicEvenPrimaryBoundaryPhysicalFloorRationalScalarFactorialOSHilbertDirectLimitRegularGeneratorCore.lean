import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularTimeAverage
import Mathlib.Tactic

/-!
# Same-root infinitesimal generator core on the regular factorial OS Hilbert sector

After the genuine `NNReal` C₀ contraction semigroup and the complete regular Hilbert sector are in
place, this file constructs the positive-time right generator, its dense time-average domain, and
the Euclidean OS Hamiltonian convention `H = -A`.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology Set
open scoped InnerProductSpace Interval

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

noncomputable def fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (t : NNReal) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  (t : ℝ)⁻¹ •
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x - x)

def FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x eta : P.fixedSlotHilbertDirectLimitRegularSubspace) : Prop :=
  Tendsto
    (fun t : NNReal => P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient x t)
    (nhdsWithin 0 (Ioi 0)) (nhds eta)

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
  unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
  have hmapzero :
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (0 : P.fixedSlotHilbertDirectLimitRegularSubspace) = 0 :=
    map_zero _
  rw [hmapzero]
  simp

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

theorem fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue x
      (P.fixedSlotHilbertDirectLimitRegularRightGenerator x) :=
  Classical.choose_spec x.property

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
    simp [add_nonneg hs t.coe_nonneg]
  rw [hs_to, hsum]
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_add_apply _ _ x

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
  have hxint : IntervalIntegrable
      (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x)
      MeasureTheory.volume 0 (h : ℝ) :=
    (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x).intervalIntegrable
      0 (h : ℝ)
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t) hxint]
  apply intervalIntegral.integral_congr
  intro s hs
  exact P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_clampedRealOrbit t x s

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
      have hlong : IntervalIntegrable
          (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x)
          MeasureTheory.volume 0 ((t : ℝ) + (h : ℝ)) :=
        (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x).intervalIntegrable
          0 ((t : ℝ) + (h : ℝ))
      have hshort : IntervalIntegrable
          (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit x)
          MeasureTheory.volume 0 (t : ℝ) :=
        (P.fixedSlotHilbertDirectLimitRegularClampedRealOrbit_continuous x).intervalIntegrable
          0 (t : ℝ)
      symm
      simpa [add_comm] using
        intervalIntegral.integral_interval_sub_left hlong hshort

noncomputable def fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (h : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
    (r : ℝ) : P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularTimePrimitive x ((h : ℝ) + r) -
    P.fixedSlotHilbertDirectLimitRegularTimePrimitive x r

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
    (P.fixedSlotHilbertDirectLimitRegularShiftedTimeIntegralPrimitive_hasDerivAt_zero h x).tendsto_slope_zero_right
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

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
