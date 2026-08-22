import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceSeparatedCovariance
import Mathlib.Tactic
import Mathlib.Tactic.FunProp

/-!
# Bounded-continuous carriers for the literal midpoint Wilson sources

The canonical midpoint covariance is already written as the ordinary Gibbs
covariance of two literal finite Wilson-source observables, with exact finite
physical-link supports.  The finite-support spatial clustering interface expects
those observables as `BoundedContinuousFunction`s.

This file supplies exactly that topological bridge.  A nonnegative primary
scalar coordinate is continuous because #1929 identifies it with the normalized
trace of one orientation-correct four-link plaquette word.  The negative
coordinate used on the left is obtained from the positive coordinate by the
actual continuous finite configuration reflection.  Finite slot vectors are
therefore continuous coordinatewise, and composition with the existing bounded
continuous fixed-slot observable gives bounded-continuous left and right Wilson
sources on the compact finite configuration space.

No Dobrushin threshold, covariance decay estimate, factorial-scale uniformity,
continuum limit, or mass-gap conclusion is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance midpointWilsonSourceBCFIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance midpointWilsonSourceBCFCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

/-- Physical time reflection is continuous on the finite compact `SU(N)`
configuration space. -/
theorem periodicHypercubicEvenSpecialUnitaryConfigurationReflection_continuous
    (H N : ℕ) :
    Continuous
      (periodicHypercubicEvenConfigurationReflection
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H) := by
  apply continuous_pi
  intro e
  unfold periodicHypercubicEvenConfigurationReflection
  by_cases he : e.2 = 0
  · simp only [he, if_true]
    fun_prop
  · simp only [he, if_false]
    fun_prop

/-- Every nonnegative physical-floor primary scalar coordinate is continuous as
a function of the full finite Wilson configuration. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_continuous_of_nonnegative
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hq : 0 ≤ q) :
    Continuous
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) q) := by
  have hword :
      Continuous
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          orientedFourEdgePlaquetteWord
            (fun k =>
              A
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
                  H latticeSpacing n q k))) := by
    unfold orientedFourEdgePlaquetteWord
    fun_prop
  have henergy :
      Continuous
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          specialUnitaryWilsonPlaquetteEnergy N
            (orientedFourEdgePlaquetteWord
              (fun k =>
                A
                  (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
                    H latticeSpacing n q k)))) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hword
  have hfun :
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) q) =
      (fun A =>
        1 - specialUnitaryWilsonPlaquetteEnergy N
          (orientedFourEdgePlaquetteWord
            (fun k =>
              A
                (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
                  H latticeSpacing n q k)))) := by
    funext A
    rw [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_apply_eq
        H N latticeSpacing n q hq A]
    rw [specialUnitaryWilsonPlaquetteEnergy_eq]
    ring
  rw [hfun]
  exact continuous_const.sub henergy

/-- The reflected negative coordinate `-q`, for `q ≥ 0`, is continuous on the
same finite configuration space. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_neg_continuous_of_nonnegative
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hq : 0 ≤ q) :
    Continuous
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) (-q)) := by
  have hpositive :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_continuous_of_nonnegative
      H N latticeSpacing n q hq
  have hreflection :=
    periodicHypercubicEvenSpecialUnitaryConfigurationReflection_continuous H N
  have hcomposed :
      Continuous
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
            H N
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n
              (periodicHypercubicEvenConfigurationReflection H A)) q) :=
    hpositive.comp hreflection
  have hfun :
      (fun A : PeriodicHypercubicEvenEdge H →
          Matrix.specialUnitaryGroup (Fin N) ℂ =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) (-q)) =
      (fun A =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n
            (periodicHypercubicEvenConfigurationReflection H A)) q) := by
    funext A
    have hcov := congrFun
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectionCompletedReadout_configurationReflection
        H N latticeSpacing n A) q
    simpa [
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathReflection] using
      hcov.symm
  rw [hfun]
  exact hcomposed

/-- Continuity of the literal reflected-left fixed-slot Wilson source. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable_continuous
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
        H N latticeSpacing n J F) := by
  let X :=
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n)
  have hcoords :
      Continuous
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          fun q : J => X A (-q.1)) := by
    apply continuous_pi
    intro q
    simpa [X, Function.comp_apply] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_neg_continuous_of_nonnegative
        H N latticeSpacing n q.1 (hJ q.1 q.2)
  simpa [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable,
    X] using F.continuous.comp hcoords

/-- Continuity of the literal translated-right fixed-slot Wilson source. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable_continuous
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    Continuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
        H N latticeSpacing n J r F) := by
  let X :=
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath H N) ∘
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H latticeSpacing n)
  have hcoords :
      Continuous
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          fun q : J => X A ((q.1 + r) + r)) := by
    apply continuous_pi
    intro q
    have hqr : 0 ≤ (q.1 + r) + r := by
      linarith [hJ q.1 q.2, hr]
    simpa [X, Function.comp_apply] using
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_continuous_of_nonnegative
        H N latticeSpacing n ((q.1 + r) + r) hqr
  simpa [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable,
    X] using F.continuous.comp hcoords

/-- Bounded-continuous packaging of the literal reflected-left midpoint source
on the compact finite Wilson configuration space. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
        H N latticeSpacing n J F,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable_continuous
        H N latticeSpacing n J hJ F⟩

/-- Bounded-continuous packaging of the literal translated-right midpoint source
on the compact finite Wilson configuration space. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
        H N latticeSpacing n J r F,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable_continuous
        H N latticeSpacing n J hJ r hr F⟩

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF_apply
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
        H N latticeSpacing n J hJ F A =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
        H N latticeSpacing n J F A := by
  rfl

@[simp] theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF_apply
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
        H N latticeSpacing n J hJ r hr F A =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
        H N latticeSpacing n J r F A := by
  rfl

/-- The left BCF keeps exactly the canonical reflected midpoint support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J →
      A e = B e) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
        H N latticeSpacing n J hJ F A =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceBCF
        H N latticeSpacing n J hJ F B := by
  simpa using
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable_eq_of_eqOn_support
      H N latticeSpacing n J hJ F A B hAB

/-- The right BCF keeps exactly the canonical translated midpoint support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H → Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r →
      A e = B e) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
        H N latticeSpacing n J hJ r hr F A =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceBCF
        H N latticeSpacing n J hJ r hr F B := by
  simpa using
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable_eq_of_eqOn_support
      H N latticeSpacing n J hJ r hr F A B hAB

end

end MathlibAnalytic
end MGAP4D
