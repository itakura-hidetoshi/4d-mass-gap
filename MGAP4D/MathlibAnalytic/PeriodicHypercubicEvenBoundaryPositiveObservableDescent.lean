import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedTopology
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveWilsonGibbsReflectionPositivity

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace FiniteInvolutiveEdgeOrbitPartition

universe v w

variable {Edge : Type} [Fintype Edge]

/-- A full observable is negative-half independent when, at fixed shared
boundary and positive open half, changing the negative open-half coordinates
does not change its value. -/
def NegativeHalfIndependent
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    {Value : Type v} {Target : Type w}
    (f : (Edge → Value) → Target) : Prop :=
  ∀ b x y₁ y₂,
    f (P.boundaryFiberedAssemble b x y₁) =
      f (P.boundaryFiberedAssemble b x y₂)

/-- A bounded continuous full observable canonically descends to shared
boundary plus positive-half coordinates after fixing an arbitrary dummy
negative-half configuration. -/
noncomputable def boundaryPositiveObservableOfFull
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value]
    (y₀ : P.OpenHalfConfiguration Value)
    (f : BoundedContinuousFunction (Edge → Value) ℝ) :
    BoundedContinuousFunction
      (P.BoundaryConfiguration Value × P.OpenHalfConfiguration Value) ℝ :=
  f.compContinuous
    ⟨(fun z => P.boundaryFiberedAssemble z.1 z.2 y₀),
      (P.continuous_boundaryFiberedAssemble Value).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))⟩

@[simp]
theorem boundaryPositiveObservableOfFull_apply
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value]
    (y₀ : P.OpenHalfConfiguration Value)
    (f : BoundedContinuousFunction (Edge → Value) ℝ)
    (b : P.BoundaryConfiguration Value)
    (x : P.OpenHalfConfiguration Value) :
    P.boundaryPositiveObservableOfFull Value y₀ f (b, x) =
      f (P.boundaryFiberedAssemble b x y₀) :=
  rfl

/-- For a negative-half-independent observable, the descended boundary-positive
observable reconstructs the original value on every full configuration.  The
dummy negative-half configuration disappears exactly. -/
theorem boundaryPositiveObservableOfFull_reconstruct
    (P : FiniteInvolutiveEdgeOrbitPartition Edge)
    (Value : Type v) [TopologicalSpace Value]
    (y₀ : P.OpenHalfConfiguration Value)
    (f : BoundedContinuousFunction (Edge → Value) ℝ)
    (hind : P.NegativeHalfIndependent (fun A => f A))
    (A : Edge → Value) :
    P.boundaryPositiveObservableOfFull Value y₀ f
        (P.boundaryRestriction A, P.positiveRestriction A) =
      f A := by
  have hcoord :
      f (P.boundaryFiberedAssemble
          (P.boundaryRestriction A)
          (P.positiveRestriction A)
          (P.negativeRestriction A)) = f A :=
    congrArg f ((P.boundaryFiberedCoordinates Value).left_inv A)
  calc
    P.boundaryPositiveObservableOfFull Value y₀ f
        (P.boundaryRestriction A, P.positiveRestriction A) =
        f (P.boundaryFiberedAssemble
          (P.boundaryRestriction A)
          (P.positiveRestriction A) y₀) := rfl
    _ = f (P.boundaryFiberedAssemble
          (P.boundaryRestriction A)
          (P.positiveRestriction A)
          (P.negativeRestriction A)) :=
      hind _ _ _ _
    _ = f A := hcoord

end FiniteInvolutiveEdgeOrbitPartition

/-- Canonical boundary-positive descent on the even periodic lattice.  The
dummy negative-half configuration is the constant identity configuration. -/
noncomputable def periodicHypercubicEvenBoundaryPositiveObservableOfFull
    {Gauge : Type*} [Group Gauge] [TopologicalSpace Gauge]
    (H : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Gauge) ℝ) :
    BoundedContinuousFunction
      ((periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge ×
        (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge) ℝ :=
  (periodicHypercubicEvenEdgeOrbitPartition H).boundaryPositiveObservableOfFull
    Gauge (fun _ => 1) f

@[simp]
theorem periodicHypercubicEvenBoundaryPositiveObservableOfFull_apply
    {Gauge : Type*} [Group Gauge] [TopologicalSpace Gauge]
    (H : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Gauge) ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge) :
    periodicHypercubicEvenBoundaryPositiveObservableOfFull H f (b, x) =
      f ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
        b x (fun _ => 1)) :=
  rfl

/-- Negative-half independence identifies the canonical boundary-positive
descent with the original full observable. -/
theorem periodicHypercubicEvenBoundaryPositiveObservableOfFull_reconstruct
    {Gauge : Type*} [Group Gauge] [TopologicalSpace Gauge]
    (H : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Gauge) ℝ)
    (hind : (periodicHypercubicEvenEdgeOrbitPartition H).NegativeHalfIndependent
      (fun A => f A))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenBoundaryPositiveObservableOfFull H f
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
          (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) =
      f A :=
  (periodicHypercubicEvenEdgeOrbitPartition H).
    boundaryPositiveObservableOfFull_reconstruct Gauge (fun _ => 1) f hind A

/-- The boundary-positive reflected observable of the canonical descent is
exactly the ordinary full reflected product `f(A) f(theta A)`. -/
theorem periodicHypercubicEvenBoundaryPositiveFullReflectedObservable_descent_eq
    {Gauge : Type*} [Group Gauge] [TopologicalSpace Gauge]
    (H : ℕ)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H → Gauge) ℝ)
    (hind : (periodicHypercubicEvenEdgeOrbitPartition H).NegativeHalfIndependent
      (fun A => f A))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H
        (periodicHypercubicEvenBoundaryPositiveObservableOfFull H f) A =
      f A * f (periodicHypercubicEvenConfigurationReflection H A) := by
  unfold periodicHypercubicEvenBoundaryPositiveFullReflectedObservable
  rw [periodicHypercubicEvenBoundaryPositiveObservableOfFull_reconstruct
      H f hind A,
    periodicHypercubicEvenBoundaryPositiveObservableOfFull_reconstruct
      H f hind (periodicHypercubicEvenConfigurationReflection H A)]

/-- Any bounded continuous full observable that depends only on the shared
boundary and positive open half satisfies the actual finite Wilson Gibbs
Osterwalder--Schrader inequality.  No separate positivity premise is needed. -/
theorem periodicHypercubicEvenWilsonGibbs_reflectionPositive_of_negativeHalfIndependent
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ)
    (hind : (periodicHypercubicEvenEdgeOrbitPartition H).NegativeHalfIndependent
      (fun A => f A)) :
    0 ≤ ∫ A,
      f A * f (periodicHypercubicEvenConfigurationReflection H A)
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have hpos :=
    periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectionPositive_boundedContinuous
      H N hN beta hbeta
      (periodicHypercubicEvenBoundaryPositiveObservableOfFull H f)
  calc
    0 ≤ ∫ A,
        periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H
          (periodicHypercubicEvenBoundaryPositiveObservableOfFull H f) A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      hpos
    _ = ∫ A,
        f A * f (periodicHypercubicEvenConfigurationReflection H A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact
        periodicHypercubicEvenBoundaryPositiveFullReflectedObservable_descent_eq
          H f hind A

end

end MathlibAnalytic
end MGAP4D
