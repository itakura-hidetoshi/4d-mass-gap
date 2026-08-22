import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentLinearIsometry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHilbertSemigroup
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace InnerProduct

namespace MGAP4D
namespace MathlibAnalytic

local instance canonicalBoundaryTransferSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance canonicalBoundaryTransferSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance canonicalBoundaryTransferSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance canonicalBoundaryTransferSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance canonicalBoundaryTransferSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance canonicalBoundaryTransferSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

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

/-- The actual boundary-moment isometry and the represented-state embedding
have exactly the same norm on the raw OS carrier.  This is the compatibility
needed to extend the boundary realization to the completed finite-volume OS
Hilbert space. -/
theorem linearMap_norm_eq_physicalStateLinearMap_norm
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    ‖L.linearMap n F‖ =
      ‖(physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalStateLinearMap F‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  rw [linearMap_apply, Pn.physicalStateLinearMap_apply,
    physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2_norm,
    Pn.norm_physicalState]

/-- Canonical isometric realization of the *completed* finite Wilson OS Hilbert
space inside the actual shared-boundary `L²` space.

The extension is unique because represented positive-time states have dense
range.  No transfer, gap, decay, or integrability hypothesis is added here. -/
noncomputable def completedLinearIsometry
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  exact
    (L.linearMap n).extendOfIsometry
      (e := Pn.physicalStateLinearMap)
      Pn.physicalStateLinearMap_denseRange
      (L.linearMap_norm_eq_physicalStateLinearMap_norm n)

/-- On the dense represented-state family, the completed isometry is exactly
the actual Wilson boundary moment. -/
@[simp] theorem completedLinearIsometry_physicalState
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.completedLinearIsometry n
        ((physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).physicalState F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  rw [← Pn.physicalStateLinearMap_apply]
  simp [completedLinearIsometry,
    linearMap_norm_eq_physicalStateLinearMap_norm]

/-- The Hilbert adjoint of the completed boundary isometry is a left inverse on
its physical image: `J_n† J_n = I`.

This is derived from preservation of the real inner product, rather than
assumed as a separate reconstruction axiom. -/
theorem completedLinearIsometry_adjoint_apply
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ((L.completedLinearIsometry n).toContinuousLinearMap†)
        (L.completedLinearIsometry n psi) = psi := by
  apply ext_inner_left ℝ
  intro phi
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (L.completedLinearIsometry n).inner_map_map psi phi

/-- The canonical actual shared-boundary transfer at physical time `t`.

Writing `J_n` for the completed boundary-moment isometry and `T_{n,t/2}` for
the actual completed finite Wilson OS transfer, this is

`K_{n,t} = J_n T_{n,t/2} J_n†`.

The half-time convention is exactly the one used by the existing boundary-gap
interfaces.  On the orthogonal complement of the physical boundary image the
adjoint kills the vector, so no arbitrary extension of the transfer is chosen. -/
noncomputable def canonicalBoundaryTransfer
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  let J := L.completedLinearIsometry n
  J.toContinuousLinearMap.comp
    ((C.finiteOperator n (t / 2)).comp J.toContinuousLinearMap†)

/-- The canonical boundary transfer exactly intertwines the completed finite OS
operator with the completed boundary realization. -/
@[simp] theorem canonicalBoundaryTransfer_completedLinearIsometry
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    L.canonicalBoundaryTransfer C n t (L.completedLinearIsometry n psi) =
      L.completedLinearIsometry n (C.finiteOperator n (t / 2) psi) := by
  simp [canonicalBoundaryTransfer,
    completedLinearIsometry_adjoint_apply]

/-- Dense-carrier form of the completed finite Wilson OS transfer. -/
theorem finiteOperator_on_physicalState
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let Tn := C.toPositiveTimeObservableContractionSemigroup n
    C.finiteOperator n t (Pn.physicalState F) =
      Pn.physicalState (Tn.carrierTranslation t F) := by
  dsimp only
  exact
    (C.toPositiveTimeObservableContractionSemigroup n).toCarrierSemigroup
      |>.physicalOperator_on_physicalState t F

/-- Exact model-derived boundary-moment intertwining for every raw OS carrier
vector.  In particular it applies to the vacuum-centered carriers used by the
Poincaré and quadratic boundary-gap packages.

Thus, once the two algebraic boundary-moment coherence laws are available, the
legacy `boundaryTransfer` and `boundaryMoment_intertwining` fields no longer
represent independent analytic input. -/
theorem canonicalBoundaryTransfer_canonicalBoundaryMoment_intertwining
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.canonicalBoundaryTransfer C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n
        ((C.toPositiveTimeObservableContractionSemigroup n).carrierTranslation
          (t / 2) F) := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let Tn := C.toPositiveTimeObservableContractionSemigroup n
  calc
    L.canonicalBoundaryTransfer C n t
        (physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
          S D halfExtent N hN beta hbeta B hInvariant n F) =
      L.canonicalBoundaryTransfer C n t
        (L.completedLinearIsometry n (Pn.physicalState F)) := by
          rw [L.completedLinearIsometry_physicalState]
    _ = L.completedLinearIsometry n
        (C.finiteOperator n (t / 2) (Pn.physicalState F)) :=
      L.canonicalBoundaryTransfer_completedLinearIsometry C n t (Pn.physicalState F)
    _ = L.completedLinearIsometry n
        (Pn.physicalState (Tn.carrierTranslation (t / 2) F)) := by
      rw [L.finiteOperator_on_physicalState C n (t / 2) F]
    _ = physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation (t / 2) F) := by
      rw [L.completedLinearIsometry_physicalState]

/-- The canonical boundary transfer is contractive on the entire boundary
`L²` space.  This is a structural `≤ 1` estimate only; it is deliberately not
a strict vacuum-sector contraction and therefore does not assert a mass gap. -/
theorem canonicalBoundaryTransfer_norm_le
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    ‖L.canonicalBoundaryTransfer C n t v‖ ≤ ‖v‖ := by
  let J := L.completedLinearIsometry n
  have hJ : ‖J.toContinuousLinearMap‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound J.toContinuousLinearMap zero_le_one ?_
    intro psi
    simpa using (le_refl ‖psi‖)
  have hAdj : ‖J.toContinuousLinearMap†‖ ≤ 1 := by
    simpa using hJ
  have hT : ‖C.finiteOperator n (t / 2)‖ ≤ 1 :=
    C.finiteOperator_opNorm_le n (t / 2)
  change
    ‖J (C.finiteOperator n (t / 2) (J.toContinuousLinearMap† v))‖ ≤ ‖v‖
  rw [J.norm_map]
  calc
    ‖C.finiteOperator n (t / 2) (J.toContinuousLinearMap† v)‖ ≤
        ‖C.finiteOperator n (t / 2)‖ * ‖J.toContinuousLinearMap† v‖ :=
      (C.finiteOperator n (t / 2)).le_opNorm _
    _ ≤ 1 * ‖J.toContinuousLinearMap† v‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = ‖J.toContinuousLinearMap† v‖ := one_mul _
    _ ≤ ‖J.toContinuousLinearMap†‖ * ‖v‖ :=
      (J.toContinuousLinearMap†).le_opNorm v
    _ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right hAdj (norm_nonneg _)
    _ = ‖v‖ := one_mul _

/-- Operator-norm form of the canonical boundary contraction. -/
theorem canonicalBoundaryTransfer_opNorm_le
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) :
    ‖L.canonicalBoundaryTransfer C n t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound
    (L.canonicalBoundaryTransfer C n t) zero_le_one ?_
  intro v
  simpa using L.canonicalBoundaryTransfer_norm_le C n t v

/-- Boundary realization of the normalized finite-volume OS vacuum. -/
noncomputable def canonicalBoundaryVacuum
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N :=
  L.completedLinearIsometry n
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
      S D halfExtent N hN beta hbeta B hInvariant n)

/-- The canonical boundary vacuum is normalized. -/
@[simp] theorem canonicalBoundaryVacuum_norm
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    ‖L.canonicalBoundaryVacuum n‖ = 1 := by
  rw [canonicalBoundaryVacuum, LinearIsometry.norm_map,
    physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum_norm]

/-- The canonical boundary transfer fixes the normalized physical boundary
vacuum. -/
@[simp] theorem canonicalBoundaryTransfer_fixes_vacuum
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) :
    L.canonicalBoundaryTransfer C n t (L.canonicalBoundaryVacuum n) =
      L.canonicalBoundaryVacuum n := by
  rw [canonicalBoundaryVacuum,
    L.canonicalBoundaryTransfer_completedLinearIsometry,
    C.finiteOperator_fixes_vacuum]

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

end MathlibAnalytic
end MGAP4D

end
