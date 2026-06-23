import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianNonnegative
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The positive-shift lower bound controls distances on the domain of the
closed right Hamiltonian. -/
theorem lambda_mul_dist_le_dist_closedRightHamiltonianShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (psi phi : T.closedRightHamiltonian.domain) :
    lambda * dist (psi : P.PhysicalHilbert) (phi : P.PhysicalHilbert) ≤
      dist (T.closedRightHamiltonianShift lambda psi)
        (T.closedRightHamiltonianShift lambda phi) := by
  rw [dist_eq_norm, dist_eq_norm]
  calc
    lambda * ‖(psi : P.PhysicalHilbert) - (phi : P.PhysicalHilbert)‖ =
        lambda * ‖((psi - phi : T.closedRightHamiltonian.domain) :
          P.PhysicalHilbert)‖ := by simp
    _ ≤ ‖T.closedRightHamiltonianShift lambda (psi - phi)‖ :=
      T.lambda_mul_norm_le_norm_closedRightHamiltonianShift
        hlambda (psi - phi)
    _ = ‖T.closedRightHamiltonianShift lambda psi -
          T.closedRightHamiltonianShift lambda phi‖ := by
      rw [map_sub]

/-- On the range of a positive closed-Hamiltonian shift, the inverse relation
is `1 / lambda`-Lipschitz. -/
theorem dist_le_div_dist_closedRightHamiltonianShift
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (psi phi : T.closedRightHamiltonian.domain) :
    dist (psi : P.PhysicalHilbert) (phi : P.PhysicalHilbert) ≤
      dist (T.closedRightHamiltonianShift lambda psi)
        (T.closedRightHamiltonianShift lambda phi) / lambda := by
  apply (le_div_iff₀ hlambda).2
  simpa [mul_comm] using
    T.lambda_mul_dist_le_dist_closedRightHamiltonianShift
      hlambda psi phi

/-- The range of every positive shift of the closed right Hamiltonian is closed.

If shifted values form a convergent sequence, the positive-shift lower bound
makes the corresponding domain vectors Cauchy in the physical Hilbert space.
Completeness gives an ambient limit.  The shift identity then gives convergence
of the Hamiltonian values, and closedness of the Hamiltonian graph returns the
ambient limit to the operator domain. -/
theorem closedRightHamiltonianShift_range_isClosed
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    IsClosed (Set.range (T.closedRightHamiltonianShift lambda)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro yseq y hyseq hy
  choose psi hpsi using hyseq
  have hyCauchy : CauchySeq yseq := hy.cauchySeq
  have hpsiCauchy :
      CauchySeq (fun n => (psi n : P.PhysicalHilbert)) := by
    rw [Metric.cauchySeq_iff] at hyCauchy ⊢
    intro epsilon hepsilon
    rcases hyCauchy (lambda * epsilon) (mul_pos hlambda hepsilon) with
      ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hlower :=
      T.lambda_mul_dist_le_dist_closedRightHamiltonianShift
        hlambda (psi m) (psi n)
    rw [hpsi m, hpsi n] at hlower
    have hupper := hN m hm n hn
    nlinarith
  rcases cauchySeq_tendsto_of_complete hpsiCauchy with ⟨x, hx⟩
  have hscaled :
      Tendsto (fun n => lambda • (psi n : P.PhysicalHilbert)) atTop
        (nhds (lambda • x)) :=
    tendsto_const_nhds.smul hx
  have hHamiltonianEq :
      (fun n => T.closedRightHamiltonian (psi n)) =
        fun n => yseq n - lambda • (psi n : P.PhysicalHilbert) := by
    funext n
    rw [← hpsi n, T.closedRightHamiltonianShift_apply]
    module
  have hHamiltonian :
      Tendsto (fun n => T.closedRightHamiltonian (psi n)) atTop
        (nhds (y - lambda • x)) := by
    rw [hHamiltonianEq]
    exact hy.sub hscaled
  have hpair :
      Tendsto
        (fun n =>
          ((psi n : P.PhysicalHilbert),
            T.closedRightHamiltonian (psi n)))
        atTop
        (nhds (x, y - lambda • x)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hHamiltonian
  have hlimitGraph :
      (x, y - lambda • x) ∈ T.closedRightHamiltonian.graph :=
    T.closedRightHamiltonian_isClosed.mem_of_tendsto hpair
      (Filter.Eventually.of_forall fun n =>
        T.closedRightHamiltonian.mem_graph (psi n))
  rcases (LinearPMap.mem_graph_iff T.closedRightHamiltonian).1 hlimitGraph with
    ⟨z, hzBase, hzValue⟩
  refine ⟨z, ?_⟩
  rw [T.closedRightHamiltonianShift_apply, hzBase, hzValue]
  module

/-- For a positive shift of the closed right Hamiltonian, dense range is
already equivalent to surjectivity because the range has just been proved
closed. -/
theorem closedRightHamiltonianShift_surjective_iff_denseRange
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Surjective (T.closedRightHamiltonianShift lambda) ↔
      Dense (Set.range (T.closedRightHamiltonianShift lambda)) := by
  constructor
  · intro hsurj
    rw [dense_iff_closure_eq]
    have hrange :
        Set.range (T.closedRightHamiltonianShift lambda) = Set.univ := by
      ext y
      constructor
      · intro _
        exact Set.mem_univ y
      · intro _
        rcases hsurj y with ⟨psi, hpsi⟩
        exact ⟨psi, hpsi⟩
    rw [hrange, closure_univ]
  · intro hdense y
    have hclosed :=
      T.closedRightHamiltonianShift_range_isClosed hlambda
    have hclosure :
        closure (Set.range (T.closedRightHamiltonianShift lambda)) = Set.univ :=
      dense_iff_closure_eq.mp hdense
    have hrange :
        Set.range (T.closedRightHamiltonianShift lambda) = Set.univ := by
      rw [← hclosed.closure_eq, hclosure]
    have hy : y ∈ Set.range (T.closedRightHamiltonianShift lambda) := by
      rw [hrange]
      exact Set.mem_univ y
    exact hy

/-- The remaining maximal-accretivity frontier is now isolated exactly as
range density.  Once density is supplied, closedness upgrades it to full
resolvent surjectivity. -/
theorem closedRightHamiltonianShift_surjective_of_denseRange
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hdense : Dense (Set.range (T.closedRightHamiltonianShift lambda))) :
    Function.Surjective (T.closedRightHamiltonianShift lambda) :=
  (T.closedRightHamiltonianShift_surjective_iff_denseRange hlambda).2 hdense

/-- Closed-range resolvent package for the OS Hamiltonian closure. -/
theorem closedRightHamiltonian_positiveShift_closedRange_package
    (T : P.StronglyContinuousPhysicalSemigroup)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    IsClosed (Set.range (T.closedRightHamiltonianShift lambda)) ∧
      Function.Injective (T.closedRightHamiltonianShift lambda) ∧
      (Function.Surjective (T.closedRightHamiltonianShift lambda) ↔
        Dense (Set.range (T.closedRightHamiltonianShift lambda))) :=
  ⟨T.closedRightHamiltonianShift_range_isClosed hlambda,
    T.closedRightHamiltonianShift_injective hlambda,
    T.closedRightHamiltonianShift_surjective_iff_denseRange hlambda⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
