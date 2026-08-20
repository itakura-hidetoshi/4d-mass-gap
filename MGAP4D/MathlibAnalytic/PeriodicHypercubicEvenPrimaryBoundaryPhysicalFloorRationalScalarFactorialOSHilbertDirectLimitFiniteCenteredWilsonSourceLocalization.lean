import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteSmoothedCenteredGapReduction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenGibbsReflection
import Mathlib.Tactic

/-!
# Finite centered same-root forms on the actual Wilson Gibbs source

The preceding same-root reduction isolates two quantitative finite inputs:

* a common centered Euclidean-time decay rate on the selected factorial tail;
* one strictly positive centered zero-separation floor on that same tail.

Those inputs are currently written on the fixed scalar rational-path pushforwards.  This file
moves them one level closer to the bare model without changing the carrier or the centering
convention.

First we prove that the actual finite reflection-completed primary path law, and hence its scalar
plaquette pushforward, are invariant under intrinsic rational-time reflection.  We then center a
positive scalar cylinder by its own finite mean and prove the exact identity

`reflectionForm(centered F) = reflectionForm(F) - finiteMean(F)^2`.

Next the centered scalar form is pulled all the way back through the two same-root pushforwards to
the actual finite even-periodic Wilson Gibbs measure.  Thus the quantity used by the mass-gap
reduction is literally an actual Wilson-source integral

`∫ (O(A)-m) (O(theta A)-m) d mu_W(A)`.

Finally the two finite hypotheses from the preceding file are proved equivalent to versions stated
entirely with these Wilson-source centered reflected integrals.  The next model-specific step can
therefore target the already-existing boundary Gram factorization of this actual source integral,
without importing an older physical carrier or identifying a static Gram operator with Euclidean
time evolution.

No positive rate, positive floor, boundary Gram lower bound, spectral gap, numerical mass, or
old-carrier equivalence is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set

noncomputable section

local instance finiteCenteredWilsonSourceSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance finiteCenteredWilsonSourceSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteCenteredWilsonSourceSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteCenteredWilsonSourceSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteCenteredWilsonSourceSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteCenteredWilsonSourceSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual finite reflection-completed primary rational path law is exactly invariant under
intrinsic rational-time reflection.  This is source Wilson reflection invariance plus the exact
reflection covariance of the completed readout. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure_reflection_map_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measure.map
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
          H N hN beta hbeta latticeSpacing n) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
        H N hN beta hbeta latticeSpacing n := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
      (Gauge := Gauge) H latticeSpacing n
  let theta :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection
      (Gauge := Gauge) H
  let rho := periodicHypercubicEvenConfigurationReflection (Gauge := Gauge) H
  let mu :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  have hX : Measurable X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
      H Gauge latticeSpacing n
  have htheta : Measurable theta :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection_measurable H
  have hrho :=
    periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
      H N hN beta hbeta
  have hcov : theta ∘ X = X ∘ rho := by
    funext A
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_configurationReflection
        H latticeSpacing n A).symm
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
  change Measure.map theta (Measure.map X mu) = Measure.map X mu
  calc
    Measure.map theta (Measure.map X mu) = Measure.map (theta ∘ X) mu :=
      Measure.map_map htheta hX
    _ = Measure.map (X ∘ rho) mu := by rw [hcov]
    _ = Measure.map X (Measure.map rho mu) :=
      (Measure.map_map hX hrho.measurable).symm
    _ = Measure.map X mu := by rw [hrho.map_eq]

/-- The finite scalar plaquette rational-path law inherits exact intrinsic reflection invariance
from the reflection-completed primary path law. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_reflection_map_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) :
    Measure.map
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          H N hN beta hbeta latticeSpacing n) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
        H N hN beta hbeta latticeSpacing n := by
  let S := periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
  let theta := periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
  let Theta :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H
  let nu :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
      H N hN beta hbeta latticeSpacing n
  have hS : Measurable S :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable H N
  have htheta : Measurable theta :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_measurable
  have hTheta : Measurable Theta :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection_measurable H
  have hnu : Measure.map Theta nu = nu :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure_reflection_map_eq_self
      H N hN beta hbeta latticeSpacing n
  have hcov : theta ∘ S = S ∘ Theta := by
    funext x
    exact
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_reflection
        H N x).symm
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
  change Measure.map theta (Measure.map S nu) = Measure.map S nu
  calc
    Measure.map theta (Measure.map S nu) = Measure.map (theta ∘ S) nu :=
      Measure.map_map htheta hS
    _ = Measure.map (S ∘ Theta) nu := by rw [hcov]
    _ = Measure.map S (Measure.map Theta nu) :=
      (Measure.map_map hS hTheta).symm
    _ = Measure.map S nu := by rw [hnu]

/-- Reflection invariance of a scalar rational-path probability law gives equality of the
expectation of every bounded-continuous observable and its intrinsic reflection pullback. -/
theorem periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_reflectionPullback_eq_of_map_eq_self
    (mu : ProbabilityMeasure (ℚ → ℝ))
    (href :
      Measure.map
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (mu : Measure (ℚ → ℝ)) =
        (mu : Measure (ℚ → ℝ)))
    (F : BoundedContinuousFunction (ℚ → ℝ) ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback F) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu F := by
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  change
    (∫ x,
      F (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x)
      ∂(mu : Measure (ℚ → ℝ))) =
      ∫ x, F x ∂(mu : Measure (ℚ → ℝ))
  have hmap :
      (∫ y, F y
        ∂Measure.map
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (mu : Measure (ℚ → ℝ))) =
        ∫ x,
          F (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x)
          ∂(mu : Measure (ℚ → ℝ)) := by
    exact MeasureTheory.integral_map
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection_measurable.aemeasurable
      F.continuous.aestronglyMeasurable
  rw [← hmap, href]

/-- A positive scalar cylinder centered by an explicitly supplied scalar `m`, still represented as
a bounded-continuous path observable. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredPathObservableAt
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (m : ℝ) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  Cyl.pathObservable - m • (1 : BoundedContinuousFunction (ℚ → ℝ) ℝ)

/-- The intrinsic reflected integrand of the explicitly centered scalar cylinder. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionIntegrandAt
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (m : ℝ) :
    BoundedContinuousFunction (ℚ → ℝ) ℝ :=
  Cyl.centeredPathObservableAt m *
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
      (Cyl.centeredPathObservableAt m)

@[simp]
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionIntegrandAt_apply
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (m : ℝ)
    (x : ℚ → ℝ) :
    Cyl.centeredReflectionIntegrandAt m x =
      (Cyl.pathObservable x - m) *
        (Cyl.pathObservable
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection x) - m) := by
  simp [
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionIntegrandAt,
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredPathObservableAt,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_apply]

/-- Intrinsic OS reflection form of the cylinder centered by `m` against a scalar path probability
law. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionFormAt
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (m : ℝ)
    (mu : ProbabilityMeasure (ℚ → ℝ)) : ℝ :=
  periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
    (Cyl.centeredReflectionIntegrandAt m)

/-- Exact probabilistic centering identity.  If `m` is the mean of `F` and also of the reflected
observable, then the reflected form of `F-m` is `Q(F)-m^2`. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionFormAt_eq_realReflectionForm_sub_sq
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (m : ℝ)
    (mu : ProbabilityMeasure (ℚ → ℝ))
    (hmean :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
          Cyl.pathObservable = m)
    (hrefMean :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
            Cyl.pathObservable) = m) :
    Cyl.centeredReflectionFormAt m mu =
      Cyl.realReflectionForm (mu : Measure (ℚ → ℝ)) - m ^ 2 := by
  let E := periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
  let F := Cyl.pathObservable
  let RF :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback F
  have hEF : E F = m := by simpa [E, F] using hmean
  have hERF : E RF = m := by simpa [E, F, RF] using hrefMean
  have hEone : E (1 : BoundedContinuousFunction (ℚ → ℝ) ℝ) = 1 := by
    dsimp [E]
    rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
    simp
  have hexpand :
      (F - m • (1 : BoundedContinuousFunction (ℚ → ℝ) ℝ)) *
          (RF - m • (1 : BoundedContinuousFunction (ℚ → ℝ) ℝ)) =
        F * RF - m • F - m • RF +
          (m * m) • (1 : BoundedContinuousFunction (ℚ → ℝ) ℝ) := by
    ext x
    simp [F, RF,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_apply]
    ring
  change
    E
        ((F - m • (1 : BoundedContinuousFunction (ℚ → ℝ) ℝ)) *
          (RF - m • (1 : BoundedContinuousFunction (ℚ → ℝ) ℝ))) =
      E (F * RF) - m ^ 2
  rw [hexpand]
  simp only [map_add, map_sub, map_smul]
  rw [hEF, hERF, hEone]
  ring

/-- Pull a positive scalar cylinder back through the reflection-completed primary readout and the
canonical scalar plaquette map to an actual finite Wilson-source observable. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceObservable
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Cyl.pathObservable
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A))

/-- Source reflection of the pulled-back cylinder is exactly intrinsic scalar path reflection. -/
@[simp]
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceObservable_reflection
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Cyl.wilsonSourceObservable H N latticeSpacing n
        (periodicHypercubicEvenConfigurationReflection H A) =
      Cyl.pathObservable
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n A))) := by
  unfold
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceObservable
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_configurationReflection,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_reflection]

/-- Actual Wilson Gibbs source integral of the scalar cylinder centered by `m`. -/
noncomputable def
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredReflectionFormAt
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ) : ℝ :=
  ∫ A,
    (Cyl.wilsonSourceObservable H N latticeSpacing n A - m) *
      (Cyl.wilsonSourceObservable H N latticeSpacing n
        (periodicHypercubicEvenConfigurationReflection H A) - m)
    ∂(periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure

/-- The centered scalar path form is literally the centered reflected integral on the actual finite
Wilson Gibbs source from which that path law is pushed forward. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionFormAt_eq_wilsonSource
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder)
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (m : ℝ) :
    Cyl.centeredReflectionFormAt m
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
          H N hN beta hbeta latticeSpacing n) =
      Cyl.wilsonSourceCenteredReflectionFormAt
        H N hN beta hbeta latticeSpacing n m := by
  let S := periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N
  let X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n
  let G := Cyl.centeredReflectionIntegrandAt m
  let mu :=
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure
  have hS : Measurable S :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_measurable H N
  have hX : Measurable X :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_measurable
      H (Matrix.specialUnitaryGroup (Fin N) ℂ) latticeSpacing n
  have hGS : AEStronglyMeasurable (fun x => G (S x))
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
        H N hN beta hbeta latticeSpacing n) :=
    ((G.continuous.measurable.comp hS).aestronglyMeasurable)
  unfold
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionFormAt
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  rw [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_toMeasure]
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
  calc
    (∫ y, G y
      ∂Measure.map S
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
          H N hN beta hbeta latticeSpacing n)) =
        ∫ x, G (S x)
          ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
            H N hN beta hbeta latticeSpacing n := by
      exact MeasureTheory.integral_map hS.aemeasurable G.continuous.aestronglyMeasurable
    _ = ∫ A, G (S (X A)) ∂mu := by
      unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathMeasure
      exact MeasureTheory.integral_map hX.aemeasurable hGS
    _ = Cyl.wilsonSourceCenteredReflectionFormAt
          H N hN beta hbeta latticeSpacing n m := by
      unfold
        PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.wilsonSourceCenteredReflectionFormAt
      apply integral_congr_ae
      filter_upwards with A
      rw [
        PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder.centeredReflectionIntegrandAt_apply]
      change
        (Cyl.wilsonSourceObservable H N latticeSpacing n A - m) *
            (Cyl.pathObservable
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
                (S (X A))) - m) =
          (Cyl.wilsonSourceObservable H N latticeSpacing n A - m) *
            (Cyl.wilsonSourceObservable H N latticeSpacing n
              (periodicHypercubicEvenConfigurationReflection H A) - m)
      rw [Cyl.wilsonSourceObservable_reflection H N latticeSpacing n A]

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The translated literal cylinder's actual finite centered reflected integral, written directly
on the actual finite Wilson Gibbs source rather than its scalar rational-path pushforward. -/
noncomputable def fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm
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
  Cyl.wilsonSourceCenteredReflectionFormAt
    (H (L.subsequence n)) N hN
    (beta (L.subsequence n)) (hbeta (L.subsequence n))
    (fun k =>
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (L.subsequence k))
    n m

/-- The translated mean-subtracted scalar finite form is exactly its actual Wilson-source centered
reflected integral, term by term on every selected factorial scale. -/
theorem fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm_eq_wilsonSourceCentered
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) :
    P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm J h hh F n =
      P.fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm J h hh F n := by
  let K := primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J
  let G := (P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F
  let Cyl := (P.fixedSlotDataOfIndex K).fixedSlotCarrierPositiveCylinder G
  let mu :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n
  let m := (P.fixedSlotDataOfIndex K).fixedSlotCarrierFiniteMean G n
  have href :
      Measure.map
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection
          (mu : Measure (ℚ → ℝ)) =
        (mu : Measure (ℚ → ℝ)) := by
    simpa [mu] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure_reflection_map_eq_self
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n
  have hmean :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
          Cyl.pathObservable = m := by
    rfl
  have hrefMean :
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
            Cyl.pathObservable) = m := by
    calc
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback
            Cyl.pathObservable) =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation mu
          Cyl.pathObservable :=
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_reflectionPullback_eq_of_map_eq_self
          mu href Cyl.pathObservable
      _ = m := hmean
  have hcenter :=
    Cyl.centeredReflectionFormAt_eq_realReflectionForm_sub_sq m mu hmean hrefMean
  have hsource :=
    Cyl.centeredReflectionFormAt_eq_wilsonSource
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n m
  change Cyl.realReflectionForm (mu : Measure (ℚ → ℝ)) - m ^ 2 =
    P.fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm J h hh F n
  rw [← hcenter, hsource]
  rfl

/-- Wilson-source form aligned with the positive smoothing time and subsequent separation used by
#1912. -/
noncomputable def fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  P.fixedSlotCarrierFiniteTranslatedCenteredWilsonSourceReflectionForm
    J ((s : ℚ) + h) (add_nonneg s.2 hh) F n

/-- The exact finite quantity used in #1912 is termwise identical to the actual Wilson-source
centered reflected integral. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) :
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s h hh F n =
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm J s h hh F n := by
  exact
    P.fixedSlotCarrierFiniteTranslatedMeanSubtractedReflectionForm_eq_wilsonSourceCentered
      J ((s : ℚ) + h) (add_nonneg s.2 hh) F n

/-- Common finite centered decay stated directly on the actual Wilson Gibbs source integrals. -/
def FixedSlotCarrierFiniteSmoothedCenteredWilsonSourceUniformDecayAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) : Prop :=
  ∀ (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (t : NNRat),
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm
          J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n ≤
        Real.exp (-m * (t : ℝ)) *
          P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm
            J s 0 le_rfl F n

/-- The #1912 common-decay hypothesis is exactly equivalent to the same inequality written on the
actual finite Wilson Gibbs source. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt_iff_wilsonSource
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) :
    P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredWilsonSourceUniformDecayAt m := by
  constructor
  · intro hdec J s hs F t
    filter_upwards [hdec J s hs F t] with n hn
    simpa only [
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered] using hn
  · intro hdec J s hs F t
    filter_upwards [hdec J s hs F t] with n hn
    simpa only [
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered] using hn

/-- Finite noncollapse stated directly as a positive tail floor for one actual Wilson-source
centered reflected integral. -/
def FixedSlotCarrierFiniteSmoothedCenteredWilsonSourcePositiveFloor
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) : Prop :=
  ∃ v : ℝ, 0 < v ∧
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ s : NNRat, ∃ hs : 0 < s,
        ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
          ∀ᶠ n : ℕ in atTop,
            v ≤ P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm
              J s 0 le_rfl F n

/-- The #1912 noncollapse hypothesis is exactly equivalent to an eventual positive floor on one
actual Wilson-source centered reflected integral. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredPositiveFloor_iff_wilsonSource
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor ↔
      P.FixedSlotCarrierFiniteSmoothedCenteredWilsonSourcePositiveFloor := by
  constructor
  · rintro ⟨v, hv, J, s, hs, F, hfloor⟩
    refine ⟨v, hv, J, s, hs, F, ?_⟩
    filter_upwards [hfloor] with n hn
    simpa only [
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered] using hn
  · rintro ⟨v, hv, J, s, hs, F, hfloor⟩
    refine ⟨v, hv, J, s, hs, F, ?_⟩
    filter_upwards [hfloor] with n hn
    simpa only [
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered] using hn

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
