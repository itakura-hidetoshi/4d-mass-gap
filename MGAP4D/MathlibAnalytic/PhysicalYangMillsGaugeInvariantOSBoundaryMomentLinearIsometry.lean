import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSActualAdjointSynthesisBoundaryTransferGap
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance boundaryMomentIsometrySideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMomentIsometrySpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMomentIsometrySpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMomentIsometrySpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMomentIsometrySpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMomentIsometrySpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The canonical actual Wilson boundary-moment vector has exactly the same
squared norm as the Osterwalder--Schrader carrier vector which generated it.

No linear-coherence assumption is used here.  The identity is the direct chain

`boundary L² norm² = boundary moment integral = finite reflected integral
                   = OS quadratic value = OS seminorm²`.

Thus the current pointwise finite-Wilson bridge already constructs an isometry
at the level of norms; only compatibility of the independently chosen finite
pullbacks under addition and scalar multiplication is still absent. -/
theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_sq
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 = ‖F‖ ^ 2 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let hF :=
    physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment_memLp_two
      S D halfExtent N hN beta hbeta B hInvariant n F
  calc
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ ^ 2 =
      ∫ b,
        ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
          S D halfExtent N hN beta hbeta B hInvariant n F b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N) := by
      simpa [physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2, hF] using
        physicalYangMillsEvenPeriodicWilsonOSBoundaryMomentL2_norm_sq
          S D halfExtent N hN beta hbeta B hInvariant n F hF
    _ = physicalYangMillsEvenPeriodicWilsonOSFiniteReflectedIntegral
        S D halfExtent N hN beta hbeta B hInvariant n F := by
      symm
      exact
        physical_yang_mills_evenPeriodicWilsonOS_finiteReflectedIntegral_eq_boundaryMoment_norm_sq
          S D halfExtent N hN beta hbeta B hInvariant n F
          (fun b =>
            PhysicalYangMillsEvenPeriodicWilsonOSActualAdjointSynthesisBoundaryTransferGapCertificate.gram_integrable
              (S := S) (D := D) (halfExtent := halfExtent) (N := N)
              (hN := hN) (beta := beta) (hbeta := hbeta) (B := B)
              (hInvariant := hInvariant) n F b)
    _ = Pn.osQuadraticValue F := by
      symm
      exact
        physical_yang_mills_evenPeriodicWilsonOS_osQuadraticValue_eq_finiteReflectedIntegral
          S D halfExtent N hN beta hbeta B hInvariant n F
    _ = ‖F‖ ^ 2 := by
      exact Pn.osQuadraticValue_eq_norm_sq F

/-- Norm version of the canonical boundary-moment isometry. -/
theorem physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F‖ = ‖F‖ := by
  have hsq :=
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm_sq
      S D halfExtent N hN beta hbeta B hInvariant n F
  nlinarith [
    norm_nonneg
      (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F),
    norm_nonneg F]

/-- Minimal missing coherence of the current actual finite-Wilson pullback
bridge.

The present `PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge` chooses a
finite bridge separately for each quadratic observable.  Consequently the
norm-preserving canonical boundary moment is theorem-generated, but its
additivity and real homogeneity do not follow from the current bridge fields.

This structure isolates exactly those two algebraic compatibilities and adds no
measure-theoretic, integrability, decay, coercivity, or mass hypothesis. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) : Prop where
  map_add :
    ∀ (n : ℕ)
      (F G : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n (F + G) =
        physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n F +
          physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
            S D halfExtent N hN beta hbeta B hInvariant n G
  map_smul :
    ∀ (n : ℕ) (r : ℝ)
      (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Carrier),
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n (r • F) =
        r • physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Under only the two missing algebraic coherence laws, the actual Wilson
boundary-moment assignment is a genuine real-linear map. -/
noncomputable def linearMap
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N where
  toFun := fun F =>
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
      S D halfExtent N hN beta hbeta B hInvariant n F
  map_add' := L.map_add n
  map_smul' := L.map_smul n

@[simp] theorem linearMap_apply
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.linearMap n F =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F :=
  rfl

/-- The coherent canonical boundary-moment map is a Mathlib linear isometry.
The norm-preservation field is not assumed: it is exactly the theorem proved
above from the Wilson Gram / OS quadratic identities. -/
noncomputable def linearIsometry
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N where
  toLinearMap := L.linearMap n
  norm_map' := fun F =>
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm
      S D halfExtent N hN beta hbeta B hInvariant n F

@[simp] theorem linearIsometry_apply
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.linearIsometry n F =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F :=
  rfl

/-- The linear-isometric embedding still lands exactly on the actual Wilson
adjoint-synthesis output `A_φ† u_F`. -/
theorem linearIsometry_apply_eq_actualSynthesis
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.linearIsometry n F =
      physicalYangMillsEvenPeriodicWilsonOSActualBoundarySynthesisOperator
        halfExtent N hN beta hbeta n
        (physicalYangMillsEvenPeriodicWilsonOSFinitePositiveHalfObservableL2
          S D halfExtent N hN beta hbeta B hInvariant n F) := by
  rw [linearIsometry_apply]
  exact
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_eq_actualSynthesis
      S D halfExtent N hN beta hbeta B hInvariant n F

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end MathlibAnalytic
end MGAP4D

end