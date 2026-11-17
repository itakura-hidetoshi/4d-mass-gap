import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2TimeOneHaarGramSchmidtCenteredV5_PZ37ANI
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSPositiveHalfClosureHaarPathTransport
import MGAP4D.MathlibAnalytic.FiniteProductProbabilityEmbeddingRestrictionL2
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANJ — original finite Wilson beta-zero OS-null time-one first excitation

For H>0, the literal time-one spatial slice is a strict positive interior
slice, and the already-verified original boundary/open-half coordinate
equivalence reads its ACTUAL links from the open-half Haar variables.
The exact finite-product Haar coordinate embedding and the original
four-link cyclic plaquette Haar theorem then give normalized SU(2) Haar
as the conditional time-one holonomy law for EVERY fixed boundary.

ANI proved the chosen continuous Wilson Gram-Schmidt mode 1 is Haar centered.
This file connects that original mode, unchanged positive-time-one cylinder,
and ANF/ANG0 reflection Gram form without an assumed conditional Haar kernel.
At beta zero this particular PURE mode 1 has zero original Wilson OS quadratic
form for every H>0. H=0 is excluded, as its time one is an antipodal fixed
boundary, not a strict positive interior slice.

THIS IS NOT YET the nonzero OS class of the original physical
top-eigenspace-orthogonal two-mode combination; coefficient selection,
nonzero positive-beta OS norm, Wilson one-slab intertwining, and continuum
mass gap remain separate.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANJ_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength,
    periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩
local instance p4Q2PZ37ANJ_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANJ_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANJ_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANJ_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANJ_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANJ_sliceFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual positive-time-one spatial links are a finite embedding of
the original native spatial slice into the ORIGINAL positive-edge sector.
Its construction uses the certified strict interior index k=0 in Fin H. -/
noncomputable def p4Q2PZ37ANJ_timeOneOpenSpatialLinkEmbedding
    (H : ℕ) (hH : 0 < H) :
    PeriodicHypercubicEvenSpatialSliceLink H ↪
      (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge where
  toFun := fun e =>
    periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge H
      (Sum.inl ((⟨0, hH⟩ : Fin H), e))
  inj' := by
    intro e e' h
    have hh :=
      (periodicHypercubicEvenPositiveHalfOpenIndexToPositiveEdge_injective H) h
    exact congrArg Prod.snd (Sum.inl.inj hh)

/-- Read the EXACT original time-one native spatial-link field from the
positive open-half edge configuration, not from an independent artificial
one-slab copy. -/
noncomputable def p4Q2PZ37ANJ_timeOneOpenSpatialSlice
    (H : ℕ) (hH : 0 < H)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
  fun e => x (p4Q2PZ37ANJ_timeOneOpenSpatialLinkEmbedding H hH e)

/-- Original open-half normalized Haar pushes onto the actual time-one
native spatial-slice normalized Haar, using the finite product embedding. -/
theorem p4Q2PZ37ANJ_timeOneOpenSpatialSlice_measurePreserving
    (H : ℕ) (hH : 0 < H) :
    MeasurePreserving (p4Q2PZ37ANJ_timeOneOpenSpatialSlice H hH)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  let mu := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  change MeasurePreserving
    (fun x : (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge →
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        x (p4Q2PZ37ANJ_timeOneOpenSpatialLinkEmbedding H hH e))
    (Measure.pi (fun _ : (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge => mu))
    (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => mu))
  exact measurePreserving_finiteProductProbabilityEmbeddingRestriction mu
    (p4Q2PZ37ANJ_timeOneOpenSpatialLinkEmbedding H hH)

/-- Actual positive closure's time-one spatial path agrees pointwise with
the original positive OPEN-HALF links, independent of the fixed boundary.
This is the existing repository's publicly certified interior-coordinate
identity specialized to k=0. -/
theorem p4Q2PZ37ANJ_positiveClosureTimeOne_eq_openSpatialSlice
    (H : ℕ) (hH : 0 < H)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H 2 (b, x)).1 (p4Q2PZ37AMX_positiveTimeOne H) =
      p4Q2PZ37ANJ_timeOneOpenSpatialSlice H hH x := by
  funext e
  let k : Fin H := ⟨0, hH⟩
  have ht :
      p4Q2PZ37AMX_positiveTimeOne H = k.succ.castSucc := by
    apply Fin.ext
    simp [p4Q2PZ37AMX_positiveTimeOne, k]
  rw [ht]
  simpa [p4Q2PZ37ANJ_timeOneOpenSpatialSlice,
    p4Q2PZ37ANJ_timeOneOpenSpatialLinkEmbedding, k] using
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransfer_interior_apply
      H 2 b x k e)

/-- The actual original time-one positive-half cyclic plaquette holonomy,
when H>0, pushes forward the unchanged open-half Haar onto SU(2) Haar. -/
theorem p4Q2PZ37ANJ_timeOneOpenHolonomy_measurePreserving
    (H : ℕ) (hH : 0 < H) :
    MeasurePreserving
      (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 ∘
        p4Q2PZ37ANJ_timeOneOpenSpatialSlice H hH)
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
  exact (p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2).comp
    (p4Q2PZ37ANJ_timeOneOpenSpatialSlice_measurePreserving H hH)

/-- For EVERY fixed original reflection boundary b and H>0, the exact
ANC/ANF physical positive-time-one pure Wilson mode 1 has zero open-half
Haar fiber mean. No conditional density was assumed or substituted. -/
theorem p4Q2PZ37ANJ_originalTimeOneModeOne_fiberHaarMean_zero
    (H : ℕ) (hH : 0 < H)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    (∫ x, p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable
      H 0 1 (b, x)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)) = 0 := by
  let e := p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 ∘
    p4Q2PZ37ANJ_timeOneOpenSpatialSlice H hH
  have hPoint : ∀ x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2,
      p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H 0 1 (b, x) =
        specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1 (e x) := by
    intro x
    simp only [p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable,
      p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable,
      p4Q2PZ37ANA_timeOneTwoModeWilsonObservable,
      zero_mul, one_mul, zero_add]
    rw [p4Q2PZ37ANJ_positiveClosureTimeOne_eq_openSpatialSlice H hH b x]
    rfl
  have he : MeasurePreserving e
      (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
    p4Q2PZ37ANJ_timeOneOpenHolonomy_measurePreserving H hH
  calc
    (∫ x, p4Q2PZ37ANF_originalTimeOneBoundaryPositiveObservable H 0 1 (b, x)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2)) =
      ∫ x, specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1 (e x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H 2) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hPoint x
    _ = ∫ U, specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1 U
        ∂(normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
          exact he.integral_comp'
            (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1)
    _ = 0 := by
      exact p4Q2PZ37ANI_originalWilsonContinuousModeOne_haarMean_zero

/-- Concrete new OS-null witness: original full-periodic SU(2) Wilson Gibbs
OS quadratic form of the actual positive-time-one pure Gram-Schmidt mode 1
is ZERO at beta=0 for EVERY H>0. This is NOT a general-beta or H=0 claim.
The physical top-eigenspace-orthogonal coefficient pair is still separate. -/
theorem p4Q2PZ37ANJ_originalTimeOneModeOne_betaZero_OSQuadratic_eq_zero
    (H : ℕ) (hH : 0 < H)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)] :
    p4Q2PZ37ANF_originalTimeOneWilsonOSQuadratic
      H 0 (by norm_num) 0 1 = 0 := by
  apply p4Q2PZ37ANG0_originalTimeOneOSQuadratic_zero_of_openHaarMean_ae_zero
    H 0 1
  filter_upwards [] with b
  exact p4Q2PZ37ANJ_originalTimeOneModeOne_fiberHaarMean_zero H hH b

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_timeOneOpenSpatialSlice_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_positiveClosureTimeOne_eq_openSpatialSlice
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_timeOneOpenHolonomy_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalTimeOneModeOne_fiberHaarMean_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANJ_originalTimeOneModeOne_betaZero_OSQuadratic_eq_zero
