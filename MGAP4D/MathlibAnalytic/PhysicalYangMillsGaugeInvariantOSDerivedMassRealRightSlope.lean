import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassOrbitDifferentialInequality
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalOrbitContinuity
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

/-!
# Real right-neighborhood form of the physical orbit norm slope

Mathlib's scalar Gronwall theorem is stated for functions on `ℝ` and right
neighborhoods `𝓝[>] x`.  The canonical OS semigroup is parameterized by
`NNReal`.  This file supplies only the transport layer between those two time
carriers.

For nonnegative real base time `x`, the usual real right difference quotient of
`‖T_{x.toNNReal} psi‖²` is exactly the shifted `NNReal` slope already controlled
by the derived physical Yang--Mills mass.  Thus the same right-slope limit and
mass-decay upper bound hold on the real right-neighborhood filter required by a
later Gronwall application.

No spectral theorem, functional calculus, exact mass value, PVM atom, or new
physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Squared norm of the physical semigroup orbit, extended to real time by
clamping the time parameter to `NNReal`. -/
def physicalOrbitNormSqReal
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (x : ℝ) : ℝ :=
  ‖T.toPhysicalSemigroup.operator x.toNNReal psi‖ ^ 2

/-- The real-clamped squared orbit norm is continuous. -/
theorem physicalOrbitNormSqReal_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous (T.physicalOrbitNormSqReal psi) := by
  unfold physicalOrbitNormSqReal
  exact ((T.physicalOrbit_continuous psi).comp
    continuous_real_toNNReal).norm.pow 2

/-- Positive real offsets tend from the right of `x` to positive `NNReal`
offsets tending to zero. -/
theorem realRightOffsetToNNReal_tendsto
    (x : ℝ) :
    Tendsto (fun z : ℝ => (z - x).toNNReal)
      (nhdsWithin x (Ioi x))
      (nhdsWithin 0 (Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hfull :
        Tendsto (fun z : ℝ => (z - x).toNNReal)
          (nhds x) (nhds 0) := by
      have hcont :
          Continuous (fun z : ℝ => (z - x).toNNReal) :=
        continuous_real_toNNReal.comp (continuous_id.sub continuous_const)
      have hxcont :
          ContinuousAt (fun z : ℝ => (z - x).toNNReal) x :=
        hcont.continuousAt
      simpa using hxcont
    exact hfull.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hd : 0 < z - x := sub_pos.mpr hz
    have hdreal : 0 < (((z - x).toNNReal : NNReal) : ℝ) := by
      rw [Real.coe_toNNReal _ hd.le]
      exact hd
    exact_mod_cast hdreal

/-- On a positive real increment, the ordinary real slope equals the shifted
`NNReal` slope from the semigroup layer. -/
theorem physicalOrbitNormSqReal_slope_eq_shiftedSlope
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert)
    {x z : ℝ} (hx : 0 ≤ x) (hxz : x < z) :
    (z - x)⁻¹ *
        (T.physicalOrbitNormSqReal psi z -
          T.physicalOrbitNormSqReal psi x) =
      T.physicalOrbitNormSqShiftedSlope psi x.toNNReal
        (z - x).toNNReal := by
  have hz : 0 ≤ z := hx.trans (le_of_lt hxz)
  have hd : 0 ≤ z - x := sub_nonneg.mpr (le_of_lt hxz)
  have hsum :
      z.toNNReal = x.toNNReal + (z - x).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ hz,
      Real.coe_toNNReal _ hx, Real.coe_toNNReal _ hd]
    ring
  unfold physicalOrbitNormSqReal physicalOrbitNormSqShiftedSlope
  rw [← hsum, Real.coe_toNNReal _ hd]

/-- The right slope of the real-clamped squared orbit norm has the same
Hamiltonian limit as the canonical `NNReal` shifted slope. -/
theorem physicalOrbitNormSqReal_rightSlope_tendsto_rightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : ℝ) (hx : 0 ≤ x) (psi : T.rightGeneratorDomain) :
    Tendsto
      (fun z : ℝ =>
        (z - x)⁻¹ *
          (T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) z -
            T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) x))
      (nhdsWithin x (Ioi x))
      (nhds
        (-2 * inner ℝ
          (T.rightHamiltonian
            ⟨T.toPhysicalSemigroup.operator x.toNNReal
                (psi : P.PhysicalHilbert),
              T.physicalOperator_mem_rightGeneratorDomain
                x.toNNReal psi.property⟩)
          (T.toPhysicalSemigroup.operator x.toNNReal
            (psi : P.PhysicalHilbert)))) := by
  have hnn :=
    T.physicalOrbitNormSqShiftedSlope_tendsto_rightHamiltonian
      x.toNNReal psi
  have hcomp := hnn.comp (realRightOffsetToNNReal_tendsto x)
  apply hcomp.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (T.physicalOrbitNormSqReal_slope_eq_shiftedSlope
    (psi : P.PhysicalHilbert) hx hz).symm

/-- The real right slope therefore carries exactly the derived-mass decay upper
bound needed by scalar Gronwall. -/
theorem physicalOrbitNormSqReal_rightSlope_tendsto_mass_decay_upper
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (x : ℝ) (hx : 0 ≤ x) (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    Tendsto
      (fun z : ℝ =>
        (z - x)⁻¹ *
          (T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) z -
            T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) x))
      (nhdsWithin x (Ioi x))
      (nhds
        (-2 * inner ℝ
          (T.rightHamiltonian
            ⟨T.toPhysicalSemigroup.operator x.toNNReal
                (psi : P.PhysicalHilbert),
              T.physicalOperator_mem_rightGeneratorDomain
                x.toNNReal psi.property⟩)
          (T.toPhysicalSemigroup.operator x.toNNReal
            (psi : P.PhysicalHilbert)))) ∧
      (-2 * inner ℝ
          (T.rightHamiltonian
            ⟨T.toPhysicalSemigroup.operator x.toNNReal
                (psi : P.PhysicalHilbert),
              T.physicalOperator_mem_rightGeneratorDomain
                x.toNNReal psi.property⟩)
          (T.toPhysicalSemigroup.operator x.toNNReal
            (psi : P.PhysicalHilbert)) ≤
        -2 * T.physicalYangMillsMass *
          T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) x) := by
  refine ⟨T.physicalOrbitNormSqReal_rightSlope_tendsto_rightHamiltonian
    x hx psi, ?_⟩
  have hnn :=
    T.physicalOrbitNormSqShiftedSlope_tendsto_mass_decay_upper
      hP x.toNNReal psi horthogonal
  simpa [physicalOrbitNormSqReal] using hnn.2

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
