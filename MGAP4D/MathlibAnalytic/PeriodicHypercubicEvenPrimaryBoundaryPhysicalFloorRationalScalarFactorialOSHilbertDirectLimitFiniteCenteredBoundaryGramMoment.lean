import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteCenteredWilsonSourceLocalization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveBoundedMeasurableWilsonGibbsReflectionPositivity
import Mathlib.Tactic

/-!
# Centered same-root Wilson forms as boundary Gram-moment norms

The preceding layer identifies the finite centered quantities used by the same-root gap reduction
with literal reflected integrals under the actual finite Wilson Gibbs law.  This file pushes those
integrals through the already-canonical boundary-fibered Gram factorization.

For a measurable uniformly bounded observable on the reflection-fixed boundary together with the
positive open half, the actual Wilson reflected integral is proved exactly equal to the boundary
integral of the squared Bochner moment of its weighted Gram feature.

A positive scalar rational cylinder centered by an arbitrary scalar `m` is then represented by the
existing boundary-positive finite rational cylinder whenever its slots satisfy the explicit finite
half-extent admissibility receipt.  Consequently its centered Wilson-source form is exactly such a
boundary Gram-moment square integral.  The result is finally threaded into the selected factorial
fixed-slot quantities from the current same-root direct-limit construction.

No positive lower bound, uniform decay estimate, spectral gap, heat-bath identification, numerical
mass, or old-carrier equivalence is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance finiteCenteredBoundaryGramMomentSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance finiteCenteredBoundaryGramMomentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteCenteredBoundaryGramMomentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteCenteredBoundaryGramMomentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteCenteredBoundaryGramMomentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteCenteredBoundaryGramMomentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact Gram-square strengthening of boundary-positive finite Wilson reflection positivity.
The physical reflected integral is the boundary integral of squared Bochner moments of the
observable-weighted completed positive Gram feature. -/
theorem periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_integral_gramMoment_norm_sq_of_measurable_of_bound
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ)
    (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z, ‖f z‖ ≤ M) :
    (∫ A, periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H f A
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure) =
      ∫ b,
        ‖∫ x,
          periodicHypercubicEvenBoundaryObservableGramFeature
            H N hN beta hbeta (fun x => f (b, x)) b x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  rw [
    periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_boundaryIntegral_of_measurable_of_bound
      H N hN beta hbeta f hf M hM hbound]
  apply integral_congr_ae
  filter_upwards [] with b
  let fb : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ :=
    fun x => f (b, x)
  have hfb : Integrable
      (periodicHypercubicEvenBoundaryObservableGramFeature
        H N hN beta hbeta fb b)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
    simpa [fb] using
      periodicHypercubicEvenBoundaryPositiveObservableGramFeature_integrable_of_measurable_of_bound
        H N hN beta hbeta f hf M hM hbound b
  calc
    (∫ x, ∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal *
        (f (b, x) *
          f (b, periodicHypercubicEvenOpenHalfOrientationCorrection H y))
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta
          (b, (x, periodicHypercubicEvenOpenHalfOrientationCorrection H y))).toReal *
          (fb x * fb y)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa [fb] using
        (periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
          H N hN beta hbeta fb b x).symm
    _ = ‖∫ x,
          periodicHypercubicEvenBoundaryObservableGramFeature
            H N hN beta hbeta fb b x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)‖ ^ 2 :=
      periodicHypercubicEvenBoundaryObservable_corrected_iteratedIntegral_eq_norm_sq
        H N hN beta hbeta fb b hfb
    _ = ‖∫ x,
          periodicHypercubicEvenBoundaryObservableGramFeature
            H N hN beta hbeta (fun x => f (b, x)) b x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)‖ ^ 2 := by
      rfl

/-- Finite scalar-slot observable obtained by centering a positive cylinder by `m`. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredFiniteSlotObservableAt
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (m : ℝ) :
    (∀ q : Cyl.slots, ℝ) → ℝ :=
  fun v => Cyl.observable v - m

/-- Edge-valued lift of the centered finite scalar cylinder. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredPlaquetteLiftedCylinderAt
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ)
    (m : ℝ) :
    (∀ q : Cyl.slots,
      PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ :=
  periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder
    H N Cyl.slots (Cyl.centeredFiniteSlotObservableAt m)

/-- Boundary-positive representative of the current centered Wilson-source cylinder. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredBoundaryPositiveObservableAt
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N → ℝ :=
  periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
    H N latticeSpacing n Cyl.slots
      (Cyl.centeredPlaquetteLiftedCylinderAt H N m)

/-- The centered boundary-positive representative is measurable. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredBoundaryPositiveObservableAt_measurable
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ) :
    Measurable
      (Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt
        H N latticeSpacing n m) := by
  have hg : Measurable (Cyl.centeredFiniteSlotObservableAt m) := by
    exact Cyl.observable.continuous.measurable.sub measurable_const
  have hgedge : Measurable (Cyl.centeredPlaquetteLiftedCylinderAt H N m) := by
    exact
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteLiftedCylinder_measurable
        H N Cyl.slots (Cyl.centeredFiniteSlotObservableAt m) hg
  exact
    periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_measurable
      H N latticeSpacing n Cyl.slots
      (Cyl.centeredPlaquetteLiftedCylinderAt H N m) hgedge

/-- Uniform bound for the centered boundary-positive representative. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredBoundaryPositiveObservableAt_norm_le
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) :
    ‖Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt H N latticeSpacing n m z‖ ≤
      ‖Cyl.observable‖ + ‖m‖ := by
  apply
    periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_norm_le
      H N latticeSpacing n Cyl.slots
      (Cyl.centeredPlaquetteLiftedCylinderAt H N m)
      (‖Cyl.observable‖ + ‖m‖)
  · intro u
    change ‖Cyl.observable _ - m‖ ≤ ‖Cyl.observable‖ + ‖m‖
    calc
      ‖Cyl.observable _ - m‖ ≤ ‖Cyl.observable _‖ + ‖m‖ := norm_sub_le _ _
      _ ≤ ‖Cyl.observable‖ + ‖m‖ := by
        exact add_le_add_right (Cyl.observable.norm_coe_le_norm _) _
  · exact z

/-- Under explicit finite slot admissibility, the boundary-positive representative reconstructs
exactly the centered current Wilson-source observable on every full configuration. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredBoundaryPositiveObservableAt_reconstruct
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n Cyl.slots)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt H N latticeSpacing n m
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
          (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) =
      Cyl.wilsonSourceObservable H N latticeSpacing n A - m := by
  let g := Cyl.centeredFiniteSlotObservableAt m
  let gEdge := Cyl.centeredPlaquetteLiftedCylinderAt H N m
  rw [show
    Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt H N latticeSpacing n m
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
          (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) =
      periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder
        H N latticeSpacing n Cyl.slots gEdge
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
          (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) by rfl]
  rw [
    periodicHypercubicEvenBoundaryPositivePrimarySpatialPhysicalFloorRationalCylinder_reconstruct
      H N latticeSpacing n Cyl.slots hslots gEdge A]
  rw [←
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_reflectionCompleted_eq_rationalCylinder
      H latticeSpacing n Cyl.slots gEdge A
      (fun q => Cyl.slots_nonneg q.1 q.2)]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathCylinder_scalarPlaquetteLift_eq
      H N Cyl.slots g
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A)]
  rfl

/-- The centered Wilson-source form is the reflected integral of its boundary-positive
representative whenever the finite cylinder slots lie in the actual positive half. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredReflectionFormAt_eq_boundaryPositiveReflectedIntegral
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n Cyl.slots) :
    Cyl.wilsonSourceCenteredReflectionFormAt
        H N hN beta hbeta latticeSpacing n m =
      ∫ A,
        periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H
          (Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt
            H N latticeSpacing n m) A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  unfold
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredReflectionFormAt
  apply integral_congr_ae
  filter_upwards [] with A
  unfold periodicHypercubicEvenBoundaryPositiveFullReflectedObservable
  rw [Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt_reconstruct
    H N latticeSpacing n m hslots A]
  rw [Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt_reconstruct
    H N latticeSpacing n m hslots
    (periodicHypercubicEvenConfigurationReflection H A)]

/-- Exact boundary-Gram representation of one centered scalar Wilson-source form. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredReflectionFormAt_eq_boundaryGramMoment_norm_sq_integral
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ)
    (hslots :
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        H latticeSpacing n Cyl.slots) :
    Cyl.wilsonSourceCenteredReflectionFormAt
        H N hN beta hbeta latticeSpacing n m =
      ∫ b,
        ‖∫ x,
          periodicHypercubicEvenBoundaryObservableGramFeature
            H N hN beta hbeta
            (fun x =>
              Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt
                H N latticeSpacing n m (b, x)) b x
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  rw [Cyl.wilsonSourceCenteredReflectionFormAt_eq_boundaryPositiveReflectedIntegral
    H N hN beta hbeta latticeSpacing n m hslots]
  exact
    periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectedObservable_integral_eq_integral_gramMoment_norm_sq_of_measurable_of_bound
      H N hN beta hbeta
      (Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt H N latticeSpacing n m)
      (Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt_measurable
        H N latticeSpacing n m)
      (‖Cyl.observable‖ + ‖m‖)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt_norm_le
        H N latticeSpacing n m)

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Boundary-Gram moment form corresponding to the translated centered finite Wilson quantity. -/
noncomputable def fixedSlotCarrierFiniteTranslatedCenteredBoundaryGramMomentForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F
  let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
  let m := (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  let Hn := H (L.subsequence n)
  let betan := beta (L.subsequence n)
  let spacing := fun k =>
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      (L.subsequence k)
  ∫ b,
    ‖∫ x,
      periodicHypercubicEvenBoundaryObservableGramFeature
        Hn N hN betan (hbeta (L.subsequence n))
        (fun x =>
          Cyl.wilsonSourceCenteredBoundaryPositiveObservableAt
            Hn N spacing n m (b, x)) b x
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure Hn N)‖ ^ 2
    ∂(periodicHypercubicEvenBoundaryHaarMeasure Hn N)

/-- On an admissible selected factorial scale, the translated current Wilson-source form is exactly
its boundary Gram-moment square integral. -/
theorem fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm_eq_boundaryGramMoment
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ)
    (hslots :
      let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J
      let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F
      let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        (H (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n Cyl.slots) :
    P.fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm J h hh F n =
      P.fixedSlotCarrierFiniteTranslatedCenteredBoundaryGramMomentForm J h hh F n := by
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F
  let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
  let m := (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  let Hn := H (L.subsequence n)
  let betan := beta (L.subsequence n)
  let spacing := fun k =>
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      (L.subsequence k)
  change
    Cyl.wilsonSourceCenteredReflectionFormAt
        Hn N hN betan (hbeta (L.subsequence n)) spacing n m = _
  rw [Cyl.wilsonSourceCenteredReflectionFormAt_eq_boundaryGramMoment_norm_sq_integral
    Hn N hN betan (hbeta (L.subsequence n)) spacing n m hslots]
  rfl

/-- Boundary-Gram form aligned with the positive smoothing time and subsequent separation used in
#1912 and #1913. -/
noncomputable def fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  P.fixedSlotCarrierFiniteTranslatedCenteredBoundaryGramMomentForm
    J ((s : ℚ) + h) (add_nonneg s.2 hh) F n

/-- The exact finite centered quantity used by the same-root gap reduction equals the boundary
Gram-moment form on every selected scale where its translated cylinder is admissible. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eq_boundaryGramMoment
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ)
    (hslots :
      let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate
        ((s : ℚ) + h) (add_nonneg s.2 hh) J
      let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate
        ((s : ℚ) + h) (add_nonneg s.2 hh) F
      let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
      PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
        (H (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n Cyl.slots) :
    P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm J s h hh F n =
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s h hh F n := by
  exact
    P.fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm_eq_boundaryGramMoment
      J ((s : ℚ) + h) (add_nonneg s.2 hh) F n hslots

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
