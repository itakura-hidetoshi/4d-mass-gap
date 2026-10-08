import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarResidualGramLinearCombination
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# P4: physical transfer input as the exact Rayleigh receiver

PR #5270 makes the true half-density-transported posterior projection
Q_e = U.symm ∘ P_e ∘ U real linear, and identifies the Gram Rayleigh
form with the full spatial-link residual of a combined pair-Haar vector.

The remaining interface is the ORIGINAL physical one-slab receiver:
  v_f = lambda^(-1) * ((S f) o snd).
This is a real-linear function of the physical Haar-L2 input f.  We
construct its linear map explicitly from three EXISTING maps:
  normalized physical transfer S,
  physical gauge-invariant Hilbert inclusion,
  Lp.compMeasurePreservingₗ of the actual right endpoint,
and retain the exact lambda^(-1) scalar.  The real-linear pullback
is taken from the pinned mathlib API, not assumed for an arbitrary
measurable map.

The Rayleigh energy of an arbitrary physical linear combination is
then literally
  aᵀ G a = ∑_e ||v_(∑ a_i f_i) - Q_e v_(∑ a_i f_i)||².
We specialize to the actual right Krylov orbit and the three left
Gram-Schmidt modes, with orbit beta(n+1) and frozen beta(n).

No Dobrushin, new posterior law, covariance/norm identification,
positive-depth support assumption, inverse-vacuum sup bound, or
volume-independent full-link estimate is introduced. The continuum
mass gap and physical spacing-scaled generator gap remain open.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4PhysicalInputTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4PhysicalInputCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4PhysicalInputSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4PhysicalInputMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4PhysicalInputBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4PhysicalInputSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Genuine physical-to-pair-Haar receiver as a REAL linear map, using
the original physical normalized transfer, the canonical gauge-invariant
L2 inclusion, and the right-coordinate measure-preserving linear pullback.
The extra inverse top-transfer norm is NOT dropped. -/
noncomputable def normalizedPhysicalOneSlabPairHaarReceiverLinearMap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ •
    ((Lp.compMeasurePreservingₗ ℝ Prod.snd
        (spatialSlicePairHaar_snd_measurePreserving H N)).comp
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).subtype.comp
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta).toLinearMap))

/-- This linear map is exactly the already-proved half-density pair-Haar
physical receiver; no replacement or rescaling of the observable. -/
@[simp] theorem normalizedPhysicalOneSlabPairHaarReceiverLinearMap_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    normalizedPhysicalOneSlabPairHaarReceiverLinearMap H N hN beta hbeta f =
      normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f := by
  rfl

/-- The TRUE physical transfer input can be combined BEFORE applying
the half-density pair-Haar receiver, for arbitrary real coefficients. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_sum_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
        (∑ i : ι, a i • f i) =
      ∑ i : ι, a i •
        normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i) := by
  classical
  let L := normalizedPhysicalOneSlabPairHaarReceiverLinearMap H N hN beta hbeta
  have hLinear :
      L (∑ i : ι, a i • f i) = ∑ i : ι, a i • L (f i) := by
    simp only [map_sum, map_smul]
  simpa only [L, normalizedPhysicalOneSlabPairHaarReceiverLinearMap_apply] using hLinear

/-- Full original transported posterior projection acts linearly on
the SAME physical input sum; no independent joint law is introduced. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_project_sum_smul
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
      (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
        (∑ i : ι, a i • f i)) =
      ∑ i : ι, a i •
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i)) := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_sum_smul]
  exact pairHaarTransportedGroundStateSpatialLinkProjection_sum_smul
    H N hN beta hbeta e
    (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i)) a

/-- The complete true Gram Rayleigh form is the original one-link
posterior projection loss of one ACTUAL PHYSICAL INPUT combination. -/
theorem pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (a : ι → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (pairHaarSpatialLinkResidualGram H N hN beta hbeta
        (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i))) a) =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
            (∑ i : ι, a i • f i) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
              (∑ i : ι, a i • f i))‖ ^ 2 := by
  have hCombined :=
    (normalizedPhysicalOneSlabPairHaarReceiver_sum_smul
      H N hN beta hbeta f a).symm
  have hRayleigh := pairHaarSpatialLinkResidualGram_rayleigh_combined
    H N hN beta hbeta
    (fun i => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i)) a
  simpa only [hCombined] using hRayleigh

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "RightFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "LeftFactor" =>
  physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
local notation "Q" =>
  pairHaarTransportedGroundStateSpatialLinkProjection
    Hn 2 Pos (beta n) (hbeta n)
local notation "Receiver" =>
  normalizedPhysicalOneSlabPairHaarReceiver
    Hn 2 Pos (beta n) (hbeta n)

/-- Full finite right Krylov Rayleigh energy of the single actual
physical input ∑_j a_j S_fine^j 1, evaluated at frozen beta(n). -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_physicalInput
    (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : Link,
        ‖Receiver (∑ j : Fin (r + 1),
            a j • RightFactor n (j : ℕ)) -
          Q e (Receiver (∑ j : Fin (r + 1),
            a j • RightFactor n (j : ℕ)))‖ ^ 2 := by
  exact pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
    Hn 2 Pos (beta n) (hbeta n)
    (fun j : Fin (r + 1) => RightFactor n (j : ℕ)) a

/-- Full three-mode left Rayleigh energy of the ORIGINAL three
evolved physical Gram-Schmidt inputs at frozen beta(n). -/
theorem fineLeftThreeModePairHaarResidualGram_rayleigh_physicalInput
    (a : Fin 3 → ℝ) :
    star a ⬝ᵥ
      (Matrix.mulVec (fineLeftThreeModePairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      ∑ e : Link,
        ‖Receiver (∑ k : Fin 3, a k • LeftFactor n r k) -
          Q e (Receiver (∑ k : Fin 3, a k • LeftFactor n r k))‖ ^ 2 := by
  exact pairHaarSpatialLinkResidualGram_rayleigh_physicalInput
    Hn 2 Pos (beta n) (hbeta n)
    (fun k : Fin 3 => LeftFactor n r k) a

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
