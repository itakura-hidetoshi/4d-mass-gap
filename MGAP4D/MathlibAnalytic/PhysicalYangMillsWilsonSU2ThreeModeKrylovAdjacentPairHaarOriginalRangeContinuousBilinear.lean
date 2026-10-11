import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPolarizationL2Stability
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

/-!
# P4-Q2-BV: genuine continuous original Wilson Haar form on physical L² core image

BS establishes full representative-independence of the ORIGINAL physical
Wilson twelve-color mass-weighted Haar-reference polarization on the image
of the bounded strongly measurable concrete joint core in the ACTUAL
physical ground-state joint L².

BT supplies the mixed uniform norm bound
  |B(F,G)| ≤ 12 ‖T F‖₂ ‖T G‖₂,
and BU establishes quantitative two-variable and quadratic stability.

We now ACTUALLY descend B to the range of T as a genuine real bilinear
map and upgrade it with pinned mathlib `LinearMap.mkContinuous₂` to a
continuous real bilinear operator on this genuine normed L² subspace.

The representative chooser is explicitly proved sound. All mathematical
results are independent of the choice, using the proved BS congruence.
No nonphysical measure or positivity floor enters the construction.

This is a continuous form on the physical joint L² CORE IMAGE, not yet
an extension to every joint L² class (which will use the earlier density
density argument and completeness). No reverse Haar-reference coercivity or
continuum mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 1700000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Core" =>
  p4Q2BP_originalBoundedStronglyMeasurableCore H N
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "T" =>
  p4Q2BR_originalCoreToPhysicalL2Linear H N hN beta hbeta
local notation "Img" =>
  LinearMap.range T
local notation "B" =>
  p4Q2BP_originalCorePolarization H N hN beta hbeta
local notation "Q" =>
  p4Q2BP_originalCoreReference H N hN beta hbeta

/-- One concrete preimage of the physical L² class in the actual bounded
Wilson core. The resulting polarization values do NOT depend on this
classical selection, by the BS representative-invariance theorem. -/
noncomputable def p4Q2BV_originalCoreRepresentative
    (x : Img) : Core :=
  Classical.choose (LinearMap.mem_range.mp x.property)

/-- The chosen concrete representative maps to EXACTLY the supplied
original physical joint L² class. -/
theorem p4Q2BV_originalCoreRepresentative_spec
    (x : Img) :
    T (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x) =
      (x : J) :=
  Classical.choose_spec (LinearMap.mem_range.mp x.property)

/-- The LITERAL original Wilson reference polarization, now as an actual
function on the image in the physical ground-state joint Hilbert space. -/
noncomputable def p4Q2BV_originalRangePolarization
    (x y : Img) : ℝ :=
  B (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x)
    (p4Q2BV_originalCoreRepresentative H N hN beta hbeta y)

/-- Symmetry descends directly from the true original Wilson pairing. -/
theorem p4Q2BV_originalRangePolarization_symm
    (x y : Img) :
    p4Q2BV_originalRangePolarization H N hN beta hbeta x y =
      p4Q2BV_originalRangePolarization H N hN beta hbeta y x := by
  unfold p4Q2BV_originalRangePolarization
  exact p4Q2BP_originalCorePolarization_symm
    H N hN beta hbeta _ _

/-- Additivity on the L² image in the first variable. Each selection
can differ from the sum of selections, so BS's congruence is essential. -/
theorem p4Q2BV_originalRangePolarization_add_left
    (x y z : Img) :
    p4Q2BV_originalRangePolarization H N hN beta hbeta (x + y) z =
      p4Q2BV_originalRangePolarization H N hN beta hbeta x z +
        p4Q2BV_originalRangePolarization H N hN beta hbeta y z := by
  let r := p4Q2BV_originalCoreRepresentative H N hN beta hbeta
  have hEq : T (r (x + y)) = T (r x + r y) := by
    rw [p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta,
      map_add,
      p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta,
      p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta]
    rfl
  change B (r (x + y)) (r z) = B (r x) (r z) + B (r y) (r z)
  calc
    B (r (x + y)) (r z) = B (r x + r y) (r z) :=
      p4Q2BS_originalPolarization_congr_left
        H N hN beta hbeta (r (x + y)) (r x + r y) (r z) hEq
    _ = B (r x) (r z) + B (r y) (r z) :=
      p4Q2BP_originalCorePolarization_add_left
        H N hN beta hbeta (r x) (r y) (r z)

/-- Real scaling on the first variable, relying on BQ's PROVED real
homogeneity and the exact original L² representative map. -/
theorem p4Q2BV_originalRangePolarization_smul_left
    (a : ℝ) (x y : Img) :
    p4Q2BV_originalRangePolarization H N hN beta hbeta (a • x) y =
      a * p4Q2BV_originalRangePolarization H N hN beta hbeta x y := by
  let r := p4Q2BV_originalCoreRepresentative H N hN beta hbeta
  have hEq : T (r (a • x)) = T (a • r x) := by
    rw [p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta,
      map_smul,
      p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta]
    rfl
  change B (r (a • x)) (r y) = a * B (r x) (r y)
  calc
    B (r (a • x)) (r y) = B (a • r x) (r y) :=
      p4Q2BS_originalPolarization_congr_left
        H N hN beta hbeta (r (a • x)) (a • r x) (r y) hEq
    _ = a * B (r x) (r y) :=
      p4Q2BQ_originalCorePolarization_smul_left
        H N hN beta hbeta a (r x) (r y)

theorem p4Q2BV_originalRangePolarization_add_right
    (x y z : Img) :
    p4Q2BV_originalRangePolarization H N hN beta hbeta x (y + z) =
      p4Q2BV_originalRangePolarization H N hN beta hbeta x y +
        p4Q2BV_originalRangePolarization H N hN beta hbeta x z := by
  calc
    p4Q2BV_originalRangePolarization H N hN beta hbeta x (y + z) =
        p4Q2BV_originalRangePolarization H N hN beta hbeta (y + z) x :=
      p4Q2BV_originalRangePolarization_symm H N hN beta hbeta x (y + z)
    _ = p4Q2BV_originalRangePolarization H N hN beta hbeta y x +
        p4Q2BV_originalRangePolarization H N hN beta hbeta z x :=
      p4Q2BV_originalRangePolarization_add_left H N hN beta hbeta y z x
    _ = p4Q2BV_originalRangePolarization H N hN beta hbeta x y +
        p4Q2BV_originalRangePolarization H N hN beta hbeta x z := by
      rw [p4Q2BV_originalRangePolarization_symm H N hN beta hbeta y x,
        p4Q2BV_originalRangePolarization_symm H N hN beta hbeta z x]

theorem p4Q2BV_originalRangePolarization_smul_right
    (a : ℝ) (x y : Img) :
    p4Q2BV_originalRangePolarization H N hN beta hbeta x (a • y) =
      a * p4Q2BV_originalRangePolarization H N hN beta hbeta x y := by
  calc
    p4Q2BV_originalRangePolarization H N hN beta hbeta x (a • y) =
        p4Q2BV_originalRangePolarization H N hN beta hbeta (a • y) x :=
      p4Q2BV_originalRangePolarization_symm H N hN beta hbeta x (a • y)
    _ = a * p4Q2BV_originalRangePolarization H N hN beta hbeta y x :=
      p4Q2BV_originalRangePolarization_smul_left H N hN beta hbeta a y x
    _ = a * p4Q2BV_originalRangePolarization H N hN beta hbeta x y := by
      rw [p4Q2BV_originalRangePolarization_symm H N hN beta hbeta y x]

/-- Genuine bilinear form on the ACTUAL Wilson physical joint L² bounded
core IMAGE; this is not a fresh or independent Hilbert space. -/
noncomputable def p4Q2BV_originalRangeBilin :
    LinearMap.BilinMap ℝ Img ℝ :=
  LinearMap.mk₂ ℝ
    (p4Q2BV_originalRangePolarization H N hN beta hbeta)
    (p4Q2BV_originalRangePolarization_add_left H N hN beta hbeta)
    (p4Q2BV_originalRangePolarization_smul_left H N hN beta hbeta)
    (p4Q2BV_originalRangePolarization_add_right H N hN beta hbeta)
    (p4Q2BV_originalRangePolarization_smul_right H N hN beta hbeta)

/-- Mixed physical norm bound survives representative selection,
so the actual descended Wilson form on the range has norm ≤ 12. -/
theorem p4Q2BV_originalRangePolarization_norm_le
    (x y : Img) :
    ‖p4Q2BV_originalRangePolarization H N hN beta hbeta x y‖ ≤
      (12 : ℝ) * (‖x‖ * ‖y‖) := by
  let r := p4Q2BV_originalCoreRepresentative H N hN beta hbeta
  have h :=
    p4Q2BT_originalCorePolarization_abs_le_physicalL2_norm_mul
      H N hN beta hbeta (r x) (r y)
  rw [p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta,
      p4Q2BV_originalCoreRepresentative_spec H N hN beta hbeta] at h
  change ‖B (r x) (r y)‖ ≤ (12 : ℝ) * (‖x‖ * ‖y‖)
  simpa only [Real.norm_eq_abs] using h

/-- Continuous real bilinear form of the ORIGINAL physical Wilson Haar
reference on the genuine normed joint-L² core image. -/
noncomputable def p4Q2BV_originalRangeContinuousBilin :
    Img →L[ℝ] Img →L[ℝ] ℝ :=
  (p4Q2BV_originalRangeBilin H N hN beta hbeta).mkContinuous₂
    12 (fun x y => by
      change
        ‖p4Q2BV_originalRangePolarization H N hN beta hbeta x y‖ ≤
          (12 : ℝ) * ‖x‖ * ‖y‖
      convert
        p4Q2BV_originalRangePolarization_norm_le H N hN beta hbeta x y
        using 1; ring)

/-- Exact original polarization value of the continuous descended form. -/
theorem p4Q2BV_originalRangeContinuousBilin_apply
    (x y : Img) :
    p4Q2BV_originalRangeContinuousBilin H N hN beta hbeta x y =
      p4Q2BV_originalRangePolarization H N hN beta hbeta x y := rfl

/-- The continuous descended form retains the LITERAL original Wilson
mass-weighted twelve-color Haar reference on its diagonal. -/
theorem p4Q2BV_originalRangeContinuousBilin_self
    (x : Img) :
    p4Q2BV_originalRangeContinuousBilin H N hN beta hbeta x x =
      Q (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x) := by
  rw [p4Q2BV_originalRangeContinuousBilin_apply]
  change B (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x)
      (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x) =
    Q (p4Q2BV_originalCoreRepresentative H N hN beta hbeta x)
  exact p4Q2BO_originalWilsonRealPolarization_self H N hN beta hbeta _

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
