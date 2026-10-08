import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineZeroGramCollapse
import Mathlib.Tactic

/-!
# P4: exact rank-one Rayleigh form at the genuine FROZEN beta-zero law

Do not confuse two separate statements:
* beta(n+1)=0 fixes the right physical Krylov orbit (PR #5276).
* beta(n)=0 makes the actual FROZEN normalized one-slab transfer rank one.

PR #5274 proves, at frozen beta=0, that the ORIGINAL physical
pair-Haar receiver of any physical input f is the constant-input
receiver multiplied by the actual physical Haar inner product
  c_f = inner(unit, f).
Its transported posterior projection Q_e is REAL linear, and the
FULL genuine link residual sum therefore scales as c_f^2.

The earlier physical-input Rayleigh identity (#5271) is now applied to
arbitrary finite real combinations. The resulting Gram quadratic form
is EXACTLY

  a^T G a = inner(unit, sum_i a_i f_i)^2 * E_zero(unit),

where E_zero(unit) retains ALL actual spatial-link posterior residuals
of the original constant-input receiver. In particular an input sum
orthogonal to the physical constant mode has ZERO full-link
Gram Rayleigh loss at frozen beta=0.

This is a genuine finite-volume one-dimensional reduction. It neither
assumes the common constant-input residual E_zero(unit) is zero nor
claims a volume-uniform estimate at beta>0. The exact output drift,
half-density, lambda inverse, original probability law and endpoint
swap are unchanged. No Dobrushin, covariance/L2 surrogate, or
positive-depth hard support is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4FrozenZeroRayleighTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4FrozenZeroRayleighCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4FrozenZeroRayleighSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4FrozenZeroRayleighMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4FrozenZeroRayleighBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4FrozenZeroRayleighSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The original physical frozen-beta-zero posterior residual Gram
Rayleigh form is exactly the square of one physical constant-mode
coefficient times the unmodified full-link constant-input residual. -/
theorem pairHaarSpatialLinkResidualGram_zero_rayleigh_rankOne
    (H N : ℕ) (hN : 0 < N)
    {ι : Type*} [Fintype ι]
    (f : ι →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN 0 (by norm_num)
          (fun i : ι =>
            normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)))
        a) =
      (inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
        (∑ i : ι, a i • f i)) ^ 2 *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
          pairHaarTransportedGroundStateSpatialLinkProjection
            H N hN 0 (by norm_num) e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))‖ ^ 2) := by
  classical
  exact
    (pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
      H N hN 0 (by norm_num) f a).trans
      (normalizedPhysicalOneSlabPairHaarReceiver_zero_fullLinkResidual_rankOne
        H N hN (∑ i : ι, a i • f i))

/-- Consequently the exact Gram Rayleigh form vanishes if the COMBINED
physical input is orthogonal to the canonical beta-zero constant unit.
No assertion about a nonzero individual input is made. -/
theorem pairHaarSpatialLinkResidualGram_zero_rayleigh_eq_zero_of_orthogonal
    (H N : ℕ) (hN : 0 < N)
    {ι : Type*} [Fintype ι]
    (f : ι →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ)
    (hOrth :
      inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
        (∑ i : ι, a i • f i) = 0) :
    star a ⬝ᵥ
      (Matrix.mulVec
        (pairHaarSpatialLinkResidualGram H N hN 0 (by norm_num)
          (fun i : ι =>
            normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)))
        a) = 0 := by
  rw [pairHaarSpatialLinkResidualGram_zero_rayleigh_rankOne]
  simp [hOrth]

/-- If a particular physical mode is constant-orthogonal, its true
frozen-beta-zero full spatial-link Gram diagonal is zero. -/
theorem pairHaarSpatialLinkResidualGram_zero_diag_eq_zero_of_orthogonal
    (H N : ℕ) (hN : 0 < N)
    {ι : Type*} [Fintype ι]
    (f : ι →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (i : ι)
    (hOrth :
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)
        (f i) = 0) :
    pairHaarSpatialLinkResidualGram H N hN 0 (by norm_num)
      (fun j : ι =>
        normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f j))
      i i = 0 := by
  have hDiag :=
    pairHaarSpatialLinkResidualGram_diag H N hN 0 (by norm_num)
      (fun j : ι =>
        normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f j)) i
  have hExact :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_fullLinkResidual_rankOne
      H N hN (f i)
  rw [hDiag]
  rw [hExact]
  simp [hOrth]

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
