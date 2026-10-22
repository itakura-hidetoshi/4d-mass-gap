import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonAllIteratedFineKrylovNonzeroV5_OZ
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic

/-!
# P4-Q2-PB — the true normalized SU(2) Wilson Krylov Gram is Hankel

The actual finite-volume one-slab Wilson physical transfer, WITH
its genuine spatial halfweights and Gauss-law Hilbert submodule,
is symmetric after the true positive-norm normalization.
Therefore the physical Gram matrix of the actual right-Krylov
orbit (U,T_tU,T_t²U,...) is the HANKEL matrix of the genuine
scalar Wilson physical moments:

  m_n(t) = <U, T_t^n U>_Gauss-law,
  G_r(t)_{ij} = <T_t^i U,T_t^j U> = m_(i+j)(t).

This is an exact identification of the UNMODIFIED normalized
Wilson dynamics, not a surrogate moment model or an assumption
of Krylov independence. It holds at all finite lattice volumes
and all nonnegative fine couplings, including beta=0.

Mathlib's exact Hilbert Gram positivity gives positive
semidefiniteness of EVERY finite Hankel moment matrix.
Its diagonal even moments are the TRUE squared norms
of the iterated Wilson physical source.

This supplies an explicit scalar analytic target for the unresolved
rank-three question: strict positivity of the 3x3 actual Hankel
determinant built from m0..m4. The determinant's positivity
is NOT asserted here. Neither a volume-uniform coercive
lower bound nor endpoint/continuum mass gap is deduced.

No Dobrushin, altered independent-Haar posterior, sorry/admit,
or new unproved axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section ActualPhysicalWilsonMoments
variable (H : ℕ) (t : ℝ) (ht : 0 ≤ t)
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive t ht

/-- The authentic scalar physical Wilson moment of the actual
normalized one-slab SU(2) transfer and the actual Gauss-law U. -/
noncomputable def p4Q2PB_originalWilsonPhysicalMoment (m : ℕ) : ℝ :=
  inner ℝ U ((Fine ^ m) U)

/-- Original normalized physical Wilson powers have an exact
self-adjoint Hankel identity. This is an equality in the SAME
Gauss-law physical Hilbert space, not a simulated covariance. -/
theorem p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment
    (i j : ℕ) :
    inner ℝ ((Fine ^ i) U) ((Fine ^ j) U) =
      p4Q2PB_originalWilsonPhysicalMoment H t ht (i + j) := by
  have hSym :
      ((Fine : Phys →L[ℝ] Phys) : Phys →ₗ[ℝ] Phys).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 specialUnitaryTwoWilsonRankPositive t ht
  induction i generalizing j with
  | zero =>
      simp [p4Q2PB_originalWilsonPhysicalMoment]
  | succ i ih =>
      calc
        inner ℝ ((Fine ^ (i + 1)) U) ((Fine ^ j) U) =
            inner ℝ (Fine ((Fine ^ i) U)) ((Fine ^ j) U) := by
              rw [pow_succ']
              rfl
        _ = inner ℝ ((Fine ^ i) U) (Fine ((Fine ^ j) U)) :=
          hSym.apply_clm _ _
        _ = inner ℝ ((Fine ^ i) U) ((Fine ^ (j + 1)) U) := by
          rw [pow_succ']
          rfl
        _ = p4Q2PB_originalWilsonPhysicalMoment H t ht (i + (j + 1)) :=
          ih (j + 1)
        _ = p4Q2PB_originalWilsonPhysicalMoment H t ht (i + 1 + j) := by
          congr 1
          omega

/-- For EVERY finite right-Krylov depth r, the true physical
Gauss-law Hilbert Gram matrix is precisely the scalar Hankel
moment matrix of the same ORIGINAL Wilson transfer. -/
theorem p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
    (r : ℕ) :
    Matrix.gram ℝ (fun j : Fin (r + 1) => (Fine ^ (j : ℕ)) U) =
      Matrix.of (fun i j : Fin (r + 1) =>
        p4Q2PB_originalWilsonPhysicalMoment H t ht ((i : ℕ) + (j : ℕ))) := by
  ext i j
  change inner ℝ ((Fine ^ (i : ℕ)) U) ((Fine ^ (j : ℕ)) U) =
    p4Q2PB_originalWilsonPhysicalMoment H t ht ((i : ℕ) + (j : ℕ))
  exact p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht (i : ℕ) (j : ℕ)

/-- The real physical normalized Wilson moment Hankel matrix is
positive SEMIDEFINITE for every finite depth and nonnegative fine
coupling, including the exactly degenerate beta=0 regime.
Positive definite in depth two or higher is NOT asserted. -/
theorem p4Q2PB_originalWilsonPhysicalHankel_posSemidef
    (r : ℕ) :
    (Matrix.of (fun i j : Fin (r + 1) =>
      p4Q2PB_originalWilsonPhysicalMoment H t ht ((i : ℕ) + (j : ℕ)))).PosSemidef := by
  rw [← p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel]
  exact Matrix.posSemidef_gram ℝ
    (fun j : Fin (r + 1) => (Fine ^ (j : ℕ)) U)

/-- Every genuine EVEN scalar Wilson physical moment is exactly
the squared real Gauss-law Hilbert norm of that repeated normalized
fine-transfer physical source. -/
theorem p4Q2PB_originalWilsonPhysical_evenMoment_eq_normSq
    (k : ℕ) :
    p4Q2PB_originalWilsonPhysicalMoment H t ht (k + k) =
      ‖(Fine ^ k) U‖ ^ 2 := by
  have h :=
    p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht k k
  rw [real_inner_self_eq_norm_sq] at h
  exact h.symm

/-- The adjoining ODD moment is the genuine physical Hilbert
cross energy of adjacent iterated Wilson sources, not an
independently chosen posterior or statistical moment. -/
theorem p4Q2PB_originalWilsonPhysical_oddMoment_eq_adjacentInner
    (k : ℕ) :
    p4Q2PB_originalWilsonPhysicalMoment H t ht (k + (k + 1)) =
      inner ℝ ((Fine ^ k) U) ((Fine ^ (k + 1)) U) :=
  (p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment H t ht k (k + 1)).symm

end ActualPhysicalWilsonMoments
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PB_originalWilsonPhysicalKrylov_inner_eq_moment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PB_originalWilsonPhysicalHankel_posSemidef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PB_originalWilsonPhysical_evenMoment_eq_normSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PB_originalWilsonPhysical_oddMoment_eq_adjacentInner
