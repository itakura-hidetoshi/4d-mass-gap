import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateSixSpatialProductHaarRayleighConstant
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroExactTransferGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateDoobPhysicalDefect
import Mathlib.Tactic

/-!
# Beta-zero physical to pair-Haar orthogonal bridge

This unit begins the transport from the genuine physical beta-zero
top-eigenspace orthogonal sector to the literal pair-Haar left-boundary
orthogonal sector used by the exact six-spatial frame/Rayleigh theorem.

The first step is deliberately kept on the canonical beta-zero ground-state
carrier:

* at beta zero the vacuum measure is Haar and the canonical vacuum is one;
* therefore the Haar-to-vacuum isometry is onto;
* if the ambient beta-zero transfer kills a Haar vector, the Doob boundary
  operator kills its ground-state transform;
* hence the coarse left-boundary projection of its right-boundary lift is zero.

No positive-beta statement is made here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroPhysicalPairHaarBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroPhysicalPairHaarBridgeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroPhysicalPairHaarBridgeSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroPhysicalPairHaarBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroPhysicalPairHaarBridgeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroPhysicalPairHaarBridgeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At beta zero the Haar-to-vacuum isometry is onto.  The proof uses the
exact vacuum-measure equality and the a.e. identity Omega=1, rather than
introducing a second transport map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry_zero_surjective
    (H N : ℕ)
    (hN : 0 < N) :
    Function.Surjective
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
        H N hN 0 (by norm_num)) := by
  intro u
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_zero_eq_Haar
      H N hN] at u ⊢
  refine ⟨u, ?_⟩
  apply Lp.ext
  have hU :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2_coeFn
      H N hN 0 (by norm_num) u
  have hOne :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_zero_coeFn_ae_eq_one
      H N hN
  filter_upwards [hU, hOne] with A hUA hOneA
  rw [hUA]
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumFunction,
    hOneA]

/-- At beta zero, vanishing of the ambient Haar-L2 transfer image forces the
Doob boundary image of the ground-state transform to vanish.  Surjectivity of
the beta-zero ground-state transform lets the matrix-coefficient identity be
tested against every vacuum-L2 vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobHaarToVacuum_zero_eq_zero_of_ambientTransfer_zero
    (H N : ℕ)
    (hN : 0 < N)
    (f :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hf :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN 0 (by norm_num) f = 0) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
        H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
          H N hN 0 (by norm_num) f) = 0 := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
      H N hN 0 (by norm_num)
  let JR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
      H N hN 0 (by norm_num)
  let JL :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftBoundaryL2Isometry
      H N hN 0 (by norm_num)
  apply ext_inner_right ℝ
  intro v
  obtain ⟨g, rfl⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry_zero_surjective
      H N hN v
  change inner ℝ
      ((JL.toContinuousLinearMap†) (JR (U f)))
      (U g) = 0
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hpair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateBoundaryHaarToVacuum_inner_eq_ambientTransfer
      H N hN 0 (by norm_num) f g
  rw [hf, inner_zero_left, mul_zero] at hpair
  simpa [JR, JL, U] using hpair

/-- A genuine physical beta-zero top-orthogonal vector is killed already by
the ambient Haar-L2 beta-zero transfer after forgetting the Gauss-law subtype. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_apply_physicalTopOrthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN 0 (by norm_num)
        (((x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            H N) :
          Lp ℝ 2
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) = 0 := by
  have hmean :
      inner ℝ
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N)
          (((x :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              H N) :
            Lp ℝ 2
              (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) = 0 := by
    simpa only [
      ← periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_coe_eq_HaarOneL2
        H N] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal_zero_inner_constantUnit
        H N hN x)
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_apply,
    hmean,
    zero_smul]

/-- For a physical beta-zero top-orthogonal vector, the coarse left-boundary
projection of the transformed right-boundary lift is zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_zero_rightBoundary_physicalTopOrthogonal
    (H N : ℕ)
    (hN : 0 < N)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN 0 (by norm_num)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
        H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN 0 (by norm_num)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            H N hN 0 (by norm_num)
            (((x :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                H N) :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))))) = 0 := by
  let f :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) :=
    ((x :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
      H N hN 0 (by norm_num)
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
      H N hN 0 (by norm_num)
  let Q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp
      H N hN 0 (by norm_num)
  let D :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobBoundaryOperator
      H N hN 0 (by norm_num)
  have hf :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
          H N hN 0 (by norm_num) f = 0 := by
    simpa [f] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_zero_apply_physicalTopOrthogonal
        H N hN x
  have hD : D (U f) = 0 := by
    simpa [D, U] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateDoobHaarToVacuum_zero_eq_zero_of_ambientTransfer_zero
        H N hN f hf
  have hQ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateCoarseCondExp_rightBoundary
      H N hN 0 (by norm_num) (U f)
  change Q (R (U f)) = 0
  simpa [
    Q, R, U, D,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift,
    hD] using hQ

end

end MGAP4D.MathlibAnalytic
