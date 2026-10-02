import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSVacuumPairAlignmentBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySliceObservableInsertion
import Mathlib.Tactic

/-!
# The uncentered SU(N) primary-plaquette two-mode pair is physical

After #5014 the full-pair H1-D route has two structural residuals:

1. finite OS vacuum pair alignment with the selected physical top-pair line;
2. physical-pair membership of the uncentered primary-plaquette mode.

The second residual is purely kinematic. The canonical primary spatial
plaquette lives entirely on the primary reflection-fixed slice. In ordered
primary/antipodal pair coordinates its boundary-Haar two-mode vector therefore
factors as a gauge-invariant primary-slice plaquette mode tensored with
constant one.

Both factors are vectors of the finite-volume Gauss-law Hilbert carrier, so the
pair is a generator of the physical pair span and hence belongs to its Hilbert
closure.

No transfer, top-mode, beta, vacuum-alignment, gap, or decay input is used for
this physicality statement.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance sunTwoModeUncenteredPairPhysicalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sunTwoModeUncenteredPairPhysicalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sunTwoModeUncenteredPairPhysicalSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sunTwoModeUncenteredPairPhysicalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sunTwoModeUncenteredPairPhysicalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sunTwoModeUncenteredPairPhysicalSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance sunTwoModeUncenteredPairPhysicalSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

def periodicHypercubicEvenPrimarySpatialSliceZeroVertex
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceVertex H :=
  ⟨0, by rfl⟩

def periodicHypercubicEvenPrimarySpatialSliceDirectionOne :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨(1 : PeriodicHypercubicAxis), by decide⟩

def periodicHypercubicEvenPrimarySpatialSliceDirectionTwo :
    PeriodicHypercubicEvenSpatialDirection :=
  ⟨(2 : PeriodicHypercubicAxis), by decide⟩

def periodicHypercubicEvenPrimarySpatialSlicePlaquette
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialSlicePlaquette H :=
  (periodicHypercubicEvenPrimarySpatialSliceZeroVertex H,
    ⟨(periodicHypercubicEvenPrimarySpatialSliceDirectionOne,
        periodicHypercubicEvenPrimarySpatialSliceDirectionTwo), by decide⟩)

def periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge
    (H : ℕ) :
    Fin 4 → PeriodicHypercubicEvenSpatialSliceLink H :=
  ![
    (periodicHypercubicEvenPrimarySpatialSliceZeroVertex H,
      periodicHypercubicEvenPrimarySpatialSliceDirectionOne),
    (periodicHypercubicEvenSpatialSliceShift H
        (periodicHypercubicEvenPrimarySpatialSliceZeroVertex H)
        periodicHypercubicEvenPrimarySpatialSliceDirectionOne,
      periodicHypercubicEvenPrimarySpatialSliceDirectionTwo),
    (periodicHypercubicEvenSpatialSliceShift H
        (periodicHypercubicEvenPrimarySpatialSliceZeroVertex H)
        periodicHypercubicEvenPrimarySpatialSliceDirectionTwo,
      periodicHypercubicEvenPrimarySpatialSliceDirectionOne),
    (periodicHypercubicEvenPrimarySpatialSliceZeroVertex H,
      periodicHypercubicEvenPrimarySpatialSliceDirectionTwo)
  ]

theorem periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_eq_orientedFourEdge
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialSlicePlaquette H) =
      orientedFourEdgePlaquetteWord
        (fun k => A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k)) := by
  rfl

theorem periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding_eq_primarySliceLink
    (H : ℕ)
    (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k =
      periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H
        (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k) := by
  apply Subtype.ext
  fin_cases k <;> rfl

theorem periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_apply_primaryPlaquetteEdge
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (k : Fin 4) :
    (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
        (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (A, B)
        (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k) =
      A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k) := by
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding_eq_primarySliceLink
      H k]
  let edge := periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H k
  have hidx :
      periodicHypercubicEvenFixedEdgeToSpatialSliceSum H
          (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H edge) =
        Sum.inl edge := by
    exact
      (periodicHypercubicEvenFixedEdgeEquivTwoSpatialSlices H).right_inv
        (Sum.inl edge)
  change
    ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : PeriodicHypercubicEvenSpatialSliceLink H ⊕
        PeriodicHypercubicEvenSpatialSliceLink H =>
          Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (A, B))
        (periodicHypercubicEvenFixedEdgeToSpatialSliceSum H
          (periodicHypercubicEvenPrimarySpatialSliceLinkToFixedEdge H edge)) =
      A edge
  rw [hidx]
  rfl

noncomputable def periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
    (H : ℕ)
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservable H N :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A =>
        specialUnitaryWilsonContinuousTwoMode hN2 k
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
            (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)),
      by
        apply (specialUnitaryWilsonContinuousTwoMode hN2 k).continuous.comp
        unfold periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
        fun_prop⟩

theorem periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable_gaugeInvariant
    (H : ℕ)
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceObservableGaugeInvariant
      H N
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
        H hN2 k) := by
  intro γ A
  change
    specialUnitaryWilsonContinuousTwoMode hN2 k
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
            H N γ A)
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H)) =
      specialUnitaryWilsonContinuousTwoMode hN2 k
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))
  rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_gaugeTransform]
  exact
    specialUnitaryWilsonContinuousTwoMode_conjInvariant hN2 k
      (γ (periodicHypercubicEvenPrimarySpatialSlicePlaquette H).1)
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
        (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))

noncomputable def periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
    (H : ℕ)
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalSpatialSliceObservableMulOperator
      H N
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
        H hN2 k)
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable_gaugeInvariant
        H hN2 k)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)

theorem periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_coeFn
    (H : ℕ)
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    (fun A =>
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 k :
        Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      fun A =>
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
          H hN2 k A := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let a :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
      H hN2 k
  change
    (fun A =>
      periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2
        H N a (Lp.const 2 μ (1 : ℝ)) A) =ᵐ[μ]
      fun A => a A
  have hmul :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
      H N a (Lp.const 2 μ (1 : ℝ))
  have hone :
      (Lp.const 2 μ (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa using
      (Lp.coeFn_const (μ := μ) (p := (2 : ENNReal)) (c := (1 : ℝ)))
  filter_upwards [hmul, hone] with A hmulA honeA
  rw [hmulA, honeA]
  simp

theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryObservable_pairCoordinates
    (H : ℕ)
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryObservable
        H hN2 k
        ((periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (A, B)) =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
        H hN2 k A := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryObservable
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
  have hedges :
      (fun j =>
        (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
          (Matrix.specialUnitaryGroup (Fin N) ℂ)).symm (A, B)
          (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H j)) =
        (fun j => A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H j)) := by
    funext j
    exact
      periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_symm_apply_primaryPlaquetteEdge
        H N A B j
  rw [hedges]
  change
    specialUnitaryWilsonContinuousTwoMode hN2 k
        (haarFinFourCyclicPlaquetteWord
          (fun j => A
            (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H j))) =
      specialUnitaryWilsonContinuousTwoMode hN2 k
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquette H))
  rw [
    periodicHypercubicEvenPrimarySpatialSlicePlaquetteHolonomy_eq_orientedFourEdge
      H N A,
    orientedFourEdgePlaquetteWord_eq_conj_haarFinFourCyclicPlaquetteWord]
  symm
  exact
    specialUnitaryWilsonContinuousTwoMode_conjInvariant hN2 k
      (A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 0) *
        A (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H 1))
      (haarFinFourCyclicPlaquetteWord
        (fun j => A
          (periodicHypercubicEvenPrimarySpatialSlicePlaquetteEdge H j)))

theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_to_pair_eq_physicalDecomposable
    (H : ℕ)
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          H hN2 k) =
      periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2
        H N
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 k)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let e :=
    periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv H
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let f :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
      H hN2 k
  apply Lp.ext
  have hforward :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry_coeFn
      H N f
  have hboundary :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_coeFn
      H hN2 k
  have he :
      MeasurePreserving e.symm
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)
        (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
    exact MeasurePreserving.symm e
      (periodicHypercubicEvenBoundarySpatialSlicePairMeasurableEquiv_measurePreserving_specialUnitaryHaar
        H N)
  have hboundaryPair :=
    he.quasiMeasurePreserving.ae_eq hboundary
  have hboundaryPair' :
      (fun z => f (e.symm z)) =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        fun z =>
          periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryObservable
            H hN2 k (e.symm z) := by
    simpa [f, e, Function.comp_def] using hboundaryPair
  have hmode :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2_coeFn
      H hN2 k
  have hmodeFst :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hmode
  have hone :
      (Lp.const 2 μ (1 : ℝ)) =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa using
      (Lp.coeFn_const (μ := μ) (p := (2 : ENNReal)) (c := (1 : ℝ)))
  have honeSnd :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hone
  have htensor :=
    realL2ExternalTensor_coeFn
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 k :
        Lp ℝ 2 μ)
      (Lp.const 2 μ (1 : ℝ))
  filter_upwards [hforward, hboundaryPair', hmodeFst, honeSnd, htensor]
      with z hfor hbd hmodez honez hten
  change
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N f z =
      realL2ExternalTensor
        (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 k :
          Lp ℝ 2 μ)
        (Lp.const 2 μ (1 : ℝ)) z
  rw [hfor]
  change f (e.symm z) =
    realL2ExternalTensor
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 k :
        Lp ℝ 2 μ)
      (Lp.const 2 μ (1 : ℝ)) z
  rw [hbd, hten]
  change
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryObservable
        H hN2 k (e.symm z) =
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 k :
        Lp ℝ 2 μ) z.1 *
        (Lp.const 2 μ (1 : ℝ)) z.2
  have hmodez' :
      (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
        H hN2 k :
        Lp ℝ 2 μ) z.1 =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModeBoundedObservable
        H hN2 k z.1 := by
    simpa [Function.comp_def] using hmodez
  have honez' : (Lp.const 2 μ (1 : ℝ)) z.2 = 1 := by
    simpa [Function.comp_def] using honez
  rw [hmodez', honez']
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryObservable_pairCoordinates
      H hN2 k z.1 z.2]
  simp

theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_to_pair_mem_physicalPairCarrier
    (H : ℕ)
    {N : ℕ}
    (hN2 : 2 ≤ N)
    (k : Fin 2) :
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2
          H hN2 k) ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H N := by
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_to_pair_eq_physicalDecomposable
      H hN2 k]
  apply
    (Submodule.le_topologicalClosure
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan H N))
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairSpan]
  apply Submodule.subset_span
  exact
    ⟨(periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2 H hN2 k,
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N), rfl⟩

section SUNTwoModeUncenteredPhysical

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

theorem physicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier :
    PhysicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier
      (halfExtent := halfExtent) (N := N) (hN2 := hN2) := by
  intro k n
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonTwoModeBoundaryHaarL2_to_pair_mem_physicalPairCarrier
      (halfExtent n) hN2 k

theorem physicalYangMillsSUNTwoModeFullPairResiduals_of_vacuumAlignment
    (hVac :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant)) :
    PhysicalYangMillsSUNTwoModeExplicitCenteredPairPhysicalCarrier
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) ∧
      PhysicalYangMillsSUNTwoModeExplicitCenteredPairTopTopOrthogonal
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN) (hN2 := hN2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant) := by
  exact
    physicalYangMillsSUNTwoModeExplicitCenteredFullPairResiduals_of_vacuumPairTopAlignment_uncentered
      hVac
      (physicalYangMillsSUNTwoModeExplicitUncenteredPairPhysicalCarrier
        (halfExtent := halfExtent) (N := N) (hN2 := hN2))

theorem physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0_of_vacuumAlignment
    (hVac :
      PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairTopAlignment
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q) (hInvariant := hInvariant))
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (k : Fin 2) (n m : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n) ^ m)
        (physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m *
        ‖physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := N) (hN := hN) (hN2 := hN2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q) (hInvariant := hInvariant) k n‖ := by
  obtain ⟨hCarrier, hOrth⟩ :=
    physicalYangMillsSUNTwoModeFullPairResiduals_of_vacuumAlignment hVac
  exact
    physicalYangMillsSUNTwoModeExplicitCenteredBoundaryPairL2_pow_norm_le_uniform_q0
      hCarrier hOrth s hs hcut k n m

end SUNTwoModeUncenteredPhysical

end

end MathlibAnalytic
end MGAP4D
