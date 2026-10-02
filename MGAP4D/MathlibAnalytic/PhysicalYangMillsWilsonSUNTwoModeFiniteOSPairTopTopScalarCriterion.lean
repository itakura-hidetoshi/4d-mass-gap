import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSFullPairNonTopQ0Bridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceSimplicity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalVacuumSector
import Mathlib.Tactic

/-!
# Scalar criterion for the completed physical pair top-top orthogonal sector

Top-eigenspace simplicity collapses the one-slice fixed sector to one real line.
Consequently every decomposable generator of the pair top-top block is a scalar
multiple of the selected pair vacuum Omega_top tensor Omega_top.

Because orthogonal complements are unchanged by topological closure, membership
in the completed top-top orthogonal sector is therefore equivalent to one
scalar matrix coefficient:

  x in TopTop^perp  iff  <Omega_top tensor Omega_top, x> = 0.

The final section specializes this criterion to the explicit centered SU(N)
two-mode pair vectors of #5009. Thus the second H1-D full-pair residual is
reduced from submodule membership to a literal scalar equation.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance pairTopTopScalarCriterionTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance pairTopTopScalarCriterionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance pairTopTopScalarCriterionSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance pairTopTopScalarCriterionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance pairTopTopScalarCriterionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance pairTopTopScalarCriterionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance pairTopTopScalarCriterionSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section PairTopTopScalarCriterion

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "mu" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N

local notation "F" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N

local notation "PairTop" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
    H N hN beta hbeta

local notation "TTspan" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan
    H N hN beta hbeta

local notation "TT" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
    H N hN beta hbeta

/-- Every full-top decomposable pair is a scalar multiple of the selected pair
vacuum once one-slice top-eigenspace simplicity is available. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2_exists_smul_pairTopMode
    (u v : F) :
    exists c : ℝ,
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2
          H N hN beta hbeta u v =
        c • PairTop := by
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H N hN beta hbeta
  have hF :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
          H N hN beta hbeta =
        ℝ ∙ omega := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_eq_span_topEigenvector
        H N hN beta hbeta
  have huSpan : (u : G) ∈ ℝ ∙ omega := by
    rw [← hF]
    exact u.property
  have hvSpan : (v : G) ∈ ℝ ∙ omega := by
    rw [← hF]
    exact v.property
  obtain ⟨cu, hcu⟩ := Submodule.mem_span_singleton.mp huSpan
  obtain ⟨cv, hcv⟩ := Submodule.mem_span_singleton.mp hvSpan
  have huL2 :
      (((u : G) : Lp ℝ 2 mu)) =
        cu • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta := by
    have h :=
      congrArg (fun z : G => (z : Lp ℝ 2 mu)) hcu
    simpa [omega,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2] using h.symm
  have hvL2 :
      (((v : G) : Lp ℝ 2 mu)) =
        cv • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta := by
    have h :=
      congrArg (fun z : G => (z : Lp ℝ 2 mu)) hcv
    simpa [omega,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2] using h.symm
  refine ⟨cu * cv, ?_⟩
  change
    realL2ExternalTensor
        (((u : G) : Lp ℝ 2 mu))
        (((v : G) : Lp ℝ 2 mu)) =
      (cu * cv) •
        realL2ExternalTensor
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
            H N hN beta hbeta)
  calc
    realL2ExternalTensor
        (((u : G) : Lp ℝ 2 mu))
        (((v : G) : Lp ℝ 2 mu)) =
      realL2ExternalTensor
        (cu • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)
        (cv • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta) := by rw [huL2, hvL2]
    _ = cu • realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)
        (cv • periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta) :=
      realL2ExternalTensor_smul_left _ _ _
    _ = cu • (cv • realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)) := by
      rw [realL2ExternalTensor_smul_right]
    _ = (cu * cv) • realL2ExternalTensor
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopModeL2
          H N hN beta hbeta) := by
      rw [smul_smul]

/-- The algebraic full top-top block is exactly the singleton span of the
selected pair vacuum. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_eq_span_pairTopMode :
    TTspan = ℝ ∙ PairTop := by
  apply le_antisymm
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan]
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨⟨u, v⟩, rfl⟩
    obtain ⟨c, hc⟩ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopDecomposableL2_exists_smul_pairTopMode
        H N hN beta hbeta u v
    rw [hc]
    exact
      Submodule.smul_mem (ℝ ∙ PairTop) c
        (Submodule.mem_span_singleton_self PairTop)
  · rw [Submodule.span_singleton_le_iff_mem]
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan]
    apply Submodule.subset_span
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta
    have homegaTop :
        omega ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
            H N hN beta hbeta := by
      simpa [omega] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_mem_topEigenspace
          H N hN beta hbeta
    let omegaF : F := ⟨omega, homegaTop⟩
    refine ⟨(omegaF, omegaF), ?_⟩
    rfl

/-- Completed top-top orthogonality is equivalent to one scalar matrix
coefficient against the selected pair vacuum. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_orthogonal_mem_iff_pairTopMode_inner_eq_zero
    (x : PairE) :
    x ∈ TTᗮ ↔ inner ℝ PairTop x = 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure]
  rw [Submodule.orthogonal_closure]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockSpan_eq_span_pairTopMode
    H N hN beta hbeta]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right

end PairTopTopScalarCriterion

section SUNTwoModeScalarResidual

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N} {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Scalar form of the second #5009 full-pair residual. -/
def PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal : Prop :=
  ∀ (k : Fin 2) (n : ℕ),
    inner R
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) N hN (beta n) (hbeta n))
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n) = 0

/-- After top-eigenspace simplicity, the old completed-submodule orthogonality
residual is exactly the scalar pair-vacuum orthogonality condition. -/
theorem physicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal_iff_scalar :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) ↔
      PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopPairScalarOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  constructor
  · intro h k n
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_orthogonal_mem_iff_pairTopMode_inner_eq_zero
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n)).1
        (h k n)
  · intro h k n
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_orthogonal_mem_iff_pairTopMode_inner_eq_zero
        (halfExtent n) N hN (beta n) (hbeta n)
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n)).2
        (h k n)

end SUNTwoModeScalarResidual

end

end MathlibAnalytic
end MGAP4D
