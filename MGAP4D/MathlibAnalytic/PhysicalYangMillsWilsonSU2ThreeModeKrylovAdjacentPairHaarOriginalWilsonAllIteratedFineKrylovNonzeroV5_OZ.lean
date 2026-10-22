import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonPositiveFinePhysicalKrylovShiftV5_OY
import Mathlib.Tactic

/-!
# P4-Q2-OZ — genuine Wilson positive-fine iterated Krylov non-annihilation

OY proved strict positive actual one-slab Wilson physical quadratic energy
on EVERY nonzero continuous Gauss-law Haar-L² physical source at fine t>0,
and its norm-normalized transfer never annihilates a nonzero finite
Krylov source. OU/OV give the same genuine continuous pointwise
gauge-invariant representation to EVERY normalized Wilson transfer
output, even if the input was only Haar-L².

First establish the general physical statement: if a genuine physical
source f is nonzero and has a continuous gauge-invariant representative,
then its actual positive-fine normalized Wilson transfer is nonzero.
Apply this repeatedly to an actual HJ physical Krylov synthesis S_r a:
the original source is regular by OW, each subsequent normalized fine
Wilson output is regular again by OV. Hence for EVERY natural k,

   S_r a != 0  ==>  T_t^k (S_r a) != 0,

at every actual finite spatial H and every positive fine t.

Combine ON's UNCONDITIONAL genuine small-positive-fine depth-one
physical source injectivity with this analytic preservation to prove
that the true 2-mode original Wilson physical Krylov coefficient
frame stays linearly separated after EVERY shift T_t^k:

   (forall a != 0, T_t^k(S_1 a) != 0)  for every k.

Equivalently, every shifted adjacent pair (T_t^k U,T_t^(k+1) U)
is independent in the original physical Gauss-law Hilbert space,
throughout ON's actual small-positive-fine interval.
THIS DOES NOT PROVE THREE-mode independence of U,TU,T²U or a
uniform-in-H/fine/depth quantitative lower bound, and the true
Schur physical source nonzero is still OPEN.

All original Wilson posteriors, Perron halfweights, fine/frozen
couplings and genuine Gauss-law Hilbert sources are unchanged.
No Dobrushin, independent Haar posterior, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OZ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OZ_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OZ_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OZ_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OZ_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalWilsonRegularPhysicalNonannihilation
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive
local notation "Raw" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive

/-- Actual norm-normalized positive-fine Wilson physical transfer
cannot erase any nonzero REAL Gauss-law source with a genuine
continuous gauge-invariant Haar-L² representative. This is derived
from OY's strict original full Wilson quadratic, not postulated. -/
theorem p4Q2OZ_originalPositiveFine_regularPhysical_normalizedTransfer_ne_zero
    (t : ℝ) (ht : 0 < t) (f : Phys) (hf : f ≠ 0)
    (hRegular : p4Q2OT_hasGaugeContinuousRepresentative H f) :
    Fine t ht.le f ≠ 0 := by
  obtain ⟨psi, hRep, _hGauge⟩ := hRegular
  have hpsi : psi ≠ 0 :=
    p4Q2OT_originalContinuousRepresentative_ne_zero H f hf psi hRep
  have hRaw : Raw t ht.le f ≠ 0 :=
    p4Q2OY_originalPhysicalWilson_transfer_ne_zero
      H t ht f psi hRep hpsi
  have hNormNe : ‖Raw t ht.le‖⁻¹ ≠ 0 :=
    inv_ne_zero
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 specialUnitaryTwoWilsonRankPositive t ht.le).ne'
  intro hFine
  change ‖Raw t ht.le‖⁻¹ • Raw t ht.le f = 0 at hFine
  have hRawZero : Raw t ht.le f = 0 :=
    (smul_eq_zero.mp hFine).resolve_left hNormNe
  exact hRaw hRawZero

end OriginalWilsonRegularPhysicalNonannihilation

section ActualWilsonRepeatedFineKrylov
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)
local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "S" => p4Q2HJ_actualRightPhysicalSourceSynthesis
  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n

/-- Every positive-fine iterate of the genuine HJ right-Krylov
physical source is itself a genuine continuous, pointwise SU(2)
gauge-invariant Haar-L² source. At k=0 this is OW; for k>=1
the actual full one-slab normalized Wilson smoothing OU/OV. -/
theorem p4Q2OZ_actualAllDepth_allIterates_hasGaugeContinuousRepresentative
    (r : ℕ) (a : Fin (r + 1) → ℝ) (k : ℕ) :
    p4Q2OT_hasGaugeContinuousRepresentative Hn
      ((Fine ^ k) (S r a)) := by
  cases k with
  | zero =>
      change p4Q2OT_hasGaugeContinuousRepresentative Hn (S r a)
      exact p4Q2OW_actualAllDepth_source_hasGaugeContinuousRepresentative
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a
  | succ j =>
      have hPow :
          (Fine ^ (j + 1)) (S r a) = Fine ((Fine ^ j) (S r a)) := by
        rw [pow_succ']
        rfl
      rw [hPow]
      exact
        p4Q2OV_originalNormalizedPhysicalTransfer_hasGaugeContinuousRepresentative
          Hn (beta (n + 1)) (hbeta (n + 1))
          ((Fine ^ j) (S r a))

/-- No nonzero original genuine Wilson finite-Krylov physical
source can vanish after ANY natural number of strictly-positive
fine Wilson transfer steps. This is stronger than OY's one-step
nonannihilation, and needs no third-rank or volume-uniform input. -/
theorem p4Q2OZ_actualPositiveFine_allDepth_allIterates_nonzero
    (ht : 0 < beta (n + 1))
    (r : ℕ) (a : Fin (r + 1) → ℝ)
    (hSource : S r a ≠ 0) (k : ℕ) :
    (Fine ^ k) (S r a) ≠ 0 := by
  induction k with
  | zero =>
      simpa using hSource
  | succ k hk =>
      have hRegular :=
        p4Q2OZ_actualAllDepth_allIterates_hasGaugeContinuousRepresentative
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a k
      have hNext :=
        p4Q2OZ_originalPositiveFine_regularPhysical_normalizedTransfer_ne_zero
          Hn (beta (n + 1)) ht ((Fine ^ k) (S r a)) hk hRegular
      have hPow :
          (Fine ^ (k + 1)) (S r a) = Fine ((Fine ^ k) (S r a)) := by
        rw [pow_succ']
        rfl
      rw [hPow]
      exact hNext

/-- ON's genuine two-context depth-one minor proves injectivity
of the TRUE original S_1 source for sufficiently small positive fine.
The strictly positive original Wilson kernel then proves every
repeatedly shifted source T_t^k(S_1 a) remains nonzero whenever the
REAL two signed coefficients a are nonzero: an actual shifted
adjacent-two-mode rank-2 physical witness for EVERY k.
There is no rank-3 physical conclusion and no k/H-uniform constant. -/
theorem p4Q2OZ_actualSmallFine_allIteratedDepthOne_twoMode_physicalNonzero
    (hFrozen : 0 < beta n) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∀ k : ℕ, ∀ a : Fin (1 + 1) → ℝ, a ≠ 0 →
          (Fine ^ k) (S 1 a) ≠ 0) := by
  obtain ⟨delta, hdelta, hInject⟩ :=
    p4Q2ON_actualDepthOne_smallFine_fullGI_and_physicalSource_injective
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro ht hsmall k a ha
  have hSInj : Function.Injective (S 1) := (hInject ht hsmall).2
  have hSource : S 1 a ≠ 0 := by
    intro hS
    have hEq : S 1 a = S 1 (0 : Fin (1 + 1) → ℝ) := by
      simpa only [map_zero] using hS
    exact ha (hSInj hEq)
  exact p4Q2OZ_actualPositiveFine_allDepth_allIterates_nonzero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n ht 1 a hSource k

end ActualWilsonRepeatedFineKrylov
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OZ_originalPositiveFine_regularPhysical_normalizedTransfer_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OZ_actualAllDepth_allIterates_hasGaugeContinuousRepresentative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OZ_actualPositiveFine_allDepth_allIterates_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OZ_actualSmallFine_allIteratedDepthOne_twoMode_physicalNonzero
