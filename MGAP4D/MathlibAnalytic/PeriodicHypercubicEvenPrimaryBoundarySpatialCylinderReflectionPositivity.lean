import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryTemporalHalfSectorGeometry
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveBoundedMeasurableWilsonGibbsReflectionPositivity
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedTopology
import Mathlib.Tactic

/-!
# One-sided primary-boundary spatial cylinders and finite Wilson OS positivity

The full reflection-fixed boundary of the even periodic lattice contains both
the primary slice at time residue `0` and the antipodal slice at residue
`H + 1`.  The preceding geometry theorem shows that positive temporal
translation treats these two fixed slices differently, so the full boundary
vacuum readout cannot simply be declared positive-half local.

This file builds the one-sided object that the geometry actually supports.
We retain only spatial edges on the primary fixed slice, translate those edges
forward by an integer time `k`, and read them from the same actual finite Wilson
configuration.  For `k <= H`, every such translated edge is boundary/positive
and therefore independent of the negative open-half coordinate.

Consequently every bounded measurable scalar cylinder of this one-sided readout
has a canonical measurable boundary-positive representative.  The bounded
measurable Wilson Gram theorem then gives its actual finite-volume
Osterwalder--Schrader inequality.

No locality premise, reflection-positivity premise, continuum premise, scale
relation, Hamiltonian premise, or spectral premise is added.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Spatial edges on the primary reflection-fixed slice.  Time-directed links
are excluded because the fixed edge sector consists of spatial links on the two
fixed time slices. -/
abbrev PeriodicHypercubicEvenPrimarySpatialBoundaryEdge (H : ℕ) :=
  {e : PeriodicHypercubicEvenEdge H // e.2 ≠ 0 ∧ (e.1 0).val = 0}

/-- Read all primary spatial boundary edges after translating them forward by
`k` lattice time units.  This is a direct readout from the actual full finite
configuration. -/
def periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
    {Gauge : Type*}
    (H k : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge :=
  fun e =>
    A (periodicHypercubicEdgeTranslationEquiv
      (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicIntegerTemporalDisplacement
        (PeriodicHypercubicEvenSideLength H) (k : ℤ)) e.1)

/-- The one-sided primary spatial readout is measurable for every measurable
value space. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H k : ℕ) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime
        (Gauge := Gauge) H k) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- For `k <= H`, changing the negative-half coordinate of a boundary-fibered
configuration cannot change the translated primary spatial readout.  This is
the function-valued form of the pointwise geometry proved previously. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_boundaryFibered_independent_negative
    {H : ℕ} {Value : Type*}
    (k : ℕ) (hk : k ≤ H)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (x y₁ y₂ :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value) :
    periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H k
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) =
      periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H k
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) := by
  funext e
  exact
    periodicHypercubicEvenBoundaryFiberedAssemble_integerTemporalTranslate_primary_independent_negative
      b x y₁ y₂ k e.1 e.2.1 e.2.2 hk

/-- A scalar cylinder of the translated primary spatial boundary readout. -/
def periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime
    {Gauge : Type*}
    (H k : ℕ)
    (g : (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) : ℝ :=
  g (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime H k A)

/-- Measurability of a scalar primary-boundary cylinder is inherited by
composition from the coordinate readout. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime_measurable
    {Gauge : Type*} [MeasurableSpace Gauge]
    (H k : ℕ)
    (g : (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Gauge) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g) := by
  exact hg.comp
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_measurable
      (Gauge := Gauge) H k)

/-- Every primary spatial cylinder at a time `k <= H` is automatically
negative-half independent in canonical boundary-fibered coordinates. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime_boundaryFibered_independent_negative
    {H : ℕ} {Value : Type*}
    (k : ℕ) (hk : k ≤ H)
    (g : (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H → Value) → ℝ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Value)
    (x y₁ y₂ :
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Value) :
    periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₁) =
      periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b x y₂) := by
  exact congrArg g
    (periodicHypercubicEvenPrimarySpatialBoundaryReadoutAtTime_boundaryFibered_independent_negative
      k hk b x y₁ y₂)

local instance primaryBoundaryCylinderTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance primaryBoundaryCylinderCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance primaryBoundaryCylinderSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance primaryBoundaryCylinderMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance primaryBoundaryCylinderBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Canonical boundary-positive representative of a one-sided primary spatial
cylinder.  The dummy negative-half coordinate is fixed to the identity; the
preceding geometry proves that this choice disappears whenever `k <= H`. -/
noncomputable def periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime
    (H N k : ℕ)
    (g :
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) : ℝ :=
  periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g
    ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
      z.1 z.2 (fun _ => 1))

/-- The canonical boundary-positive representative is measurable whenever the
scalar cylinder on primary spatial boundary data is measurable. -/
theorem periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime_measurable
    (H N k : ℕ)
    (g :
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hg : Measurable g) :
    Measurable
      (periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime
        H N k g) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  have hassemble : Measurable
      (fun z : P.BoundaryConfiguration Gauge × P.OpenHalfConfiguration Gauge =>
        P.boundaryFiberedAssemble z.1 z.2 (fun _ => 1)) := by
    exact
      ((P.continuous_boundaryFiberedAssemble Gauge).comp
        (continuous_fst.prodMk
          (continuous_snd.prodMk continuous_const))).measurable
  have hcylinder : Measurable
      (periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime
        (Gauge := Gauge) H k g) :=
    periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime_measurable
      H k g hg
  exact hcylinder.comp hassemble

/-- A bound on the scalar primary-boundary cylinder is inherited verbatim by
its canonical boundary-positive representative. -/
theorem periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime_norm_le
    (H N k : ℕ)
    (g :
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (M : ℝ)
    (hbound : ∀ u, ‖g u‖ ≤ M)
    (z : PeriodicHypercubicEvenSpecialUnitaryBoundaryPositiveConfiguration H N) :
    ‖periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime
        H N k g z‖ ≤ M := by
  exact hbound _

/-- For `k <= H`, evaluating the boundary-positive representative on the
canonical boundary/positive restriction of a full configuration exactly
reconstructs the original one-sided cylinder. -/
theorem periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime_reconstruct
    (H N k : ℕ) (hk : k ≤ H)
    (g :
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime H N k g
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
          (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A) =
      periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g A := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let F : (PeriodicHypercubicEvenEdge H → Gauge) → ℝ :=
    periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g
  have hlocal :
      F (P.boundaryFiberedAssemble
          (P.boundaryRestriction A) (P.positiveRestriction A) (fun _ => 1)) =
        F (P.boundaryFiberedAssemble
          (P.boundaryRestriction A) (P.positiveRestriction A)
          (P.negativeRestriction A)) := by
    exact
      periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime_boundaryFibered_independent_negative
        k hk g (P.boundaryRestriction A) (P.positiveRestriction A)
        (fun _ => 1) (P.negativeRestriction A)
  have hcoord :
      F (P.boundaryFiberedAssemble
          (P.boundaryRestriction A) (P.positiveRestriction A)
          (P.negativeRestriction A)) = F A :=
    congrArg F ((P.boundaryFiberedCoordinates Gauge).left_inv A)
  calc
    periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime H N k g
        (P.boundaryRestriction A, P.positiveRestriction A) =
      F (P.boundaryFiberedAssemble
        (P.boundaryRestriction A) (P.positiveRestriction A) (fun _ => 1)) := rfl
    _ = F (P.boundaryFiberedAssemble
        (P.boundaryRestriction A) (P.positiveRestriction A)
        (P.negativeRestriction A)) := hlocal
    _ = F A := hcoord
    _ = periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g A := rfl

/-- Actual finite Wilson Osterwalder--Schrader positivity for every bounded
measurable cylinder of the primary spatial boundary translated to an integer
time `k <= H`.

The observable is read from the same finite Wilson configuration, and its
positive-half locality is generated by the exact edge-side geometry rather
than assumed. -/
theorem periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime_wilsonGibbs_reflectionPositive_boundedMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ) (hk : k ≤ H)
    (g :
      (PeriodicHypercubicEvenPrimarySpatialBoundaryEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ)
    (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ u, ‖g u‖ ≤ M) :
    0 ≤ ∫ A,
      periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g A *
        periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g
          (periodicHypercubicEvenConfigurationReflection H A)
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
  have hpos :=
    periodicHypercubicEvenBoundaryPositiveWilsonGibbs_reflectionPositive_boundedMeasurable
      H N hN beta hbeta
      (periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime
        H N k g)
      (periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime_measurable
        H N k g hg)
      M hM
      (fun z =>
        periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime_norm_le
          H N k g M hbound z)
  calc
    0 ≤ ∫ A,
        periodicHypercubicEvenBoundaryPositiveFullReflectedObservable H
          (periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime
            H N k g) A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure :=
      hpos
    _ = ∫ A,
        periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g A *
          periodicHypercubicEvenPrimarySpatialBoundaryCylinderAtTime H k g
            (periodicHypercubicEvenConfigurationReflection H A)
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).gibbsMeasure := by
      apply integral_congr_ae
      filter_upwards [] with A
      unfold periodicHypercubicEvenBoundaryPositiveFullReflectedObservable
      rw [
        periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime_reconstruct
          H N k hk g A,
        periodicHypercubicEvenBoundaryPositivePrimarySpatialCylinderAtTime_reconstruct
          H N k hk g (periodicHypercubicEvenConfigurationReflection H A)]

end

end MathlibAnalytic
end MGAP4D
