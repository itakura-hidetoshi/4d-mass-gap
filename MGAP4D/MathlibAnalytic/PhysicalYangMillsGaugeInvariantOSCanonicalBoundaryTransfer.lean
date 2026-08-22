import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSBoundaryMomentLinearIsometry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHilbertSemigroup
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.UniformSpace.Separation
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
have exactly the same norm on the raw OS carrier. -/
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

/-- The coherent raw boundary moment descends canonically through the OS
separation quotient. -/
noncomputable def separatedLinearMap
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Separated →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N := by
  let J0 := L.linearIsometry n
  have hJ0 : UniformContinuous J0 := J0.isometry.uniformContinuous
  refine
    { toFun := SeparationQuotient.lift' J0
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
    rcases SeparationQuotient.surjective_mk y with ⟨G, rfl⟩
    rw [← SeparationQuotient.mk_add,
      SeparationQuotient.lift'_mk hJ0,
      SeparationQuotient.lift'_mk hJ0,
      SeparationQuotient.lift'_mk hJ0]
    exact J0.map_add F G
  · intro r x
    rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
    rw [← SeparationQuotient.mk_smul,
      SeparationQuotient.lift'_mk hJ0,
      SeparationQuotient.lift'_mk hJ0]
    exact J0.map_smul r F

@[simp] theorem separatedLinearMap_mk
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.separatedLinearMap n (SeparationQuotient.mk F) = L.linearIsometry n F := by
  change SeparationQuotient.lift' (L.linearIsometry n) (SeparationQuotient.mk F) = _
  rw [SeparationQuotient.lift'_mk
    ((L.linearIsometry n).isometry.uniformContinuous)]

/-- The descended boundary map preserves the quotient norm exactly. -/
theorem separatedLinearMap_norm
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated) :
    ‖L.separatedLinearMap n x‖ = ‖x‖ := by
  rcases SeparationQuotient.surjective_mk x with ⟨F, rfl⟩
  rw [L.separatedLinearMap_mk]
  simpa using (L.linearIsometry n).norm_map F

/-- The actual Wilson boundary realization on the separated OS pre-Hilbert
space, as a genuine Mathlib linear isometry. -/
noncomputable def separatedLinearIsometry
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).Separated →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N where
  toLinearMap := L.separatedLinearMap n
  norm_map' := L.separatedLinearMap_norm n

@[simp] theorem separatedLinearIsometry_mk
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Carrier) :
    L.separatedLinearIsometry n (SeparationQuotient.mk F) =
      physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n F := by
  change L.separatedLinearMap n (SeparationQuotient.mk F) = _
  rw [L.separatedLinearMap_mk, linearIsometry_apply]

/-- Continuous-linear extension of the separated actual Wilson boundary
realization to the completed finite-volume OS Hilbert space.

The project pins a mathlib revision predating `ContinuousLinearMap.fromCompletion`,
so the extension is bundled directly from the stable `AddMonoidHom.extension`
primitive. -/
noncomputable def completedLinearMap
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  let J := (L.separatedLinearIsometry n).toContinuousLinearMap
  change UniformSpace.Completion Pn.Separated →L[ℝ]
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N
  refine
    { __ := J.toAddMonoidHom.extension J.continuous
      map_smul' := ?_
      cont := AddMonoidHom.continuous_extension J.toAddMonoidHom J.continuous }
  intro c x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq
      ((AddMonoidHom.continuous_extension J.toAddMonoidHom J.continuous).comp
        (continuous_const_smul c))
      (by fun_prop)) ?_
  intro a
  simp [← UniformSpace.Completion.coe_smul,
    AddMonoidHom.extension_coe J.toAddMonoidHom J.continuous]

/-- The completion extension agrees with the separated boundary isometry on
the dense canonical copy. -/
@[simp] theorem completedLinearMap_coe
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (x : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n).Separated) :
    L.completedLinearMap n
        (x : UniformSpace.Completion
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).Separated) =
      L.separatedLinearIsometry n x := by
  change
    (((L.separatedLinearIsometry n).toContinuousLinearMap.toAddMonoidHom.extension
      (L.separatedLinearIsometry n).toContinuousLinearMap.continuous) x) =
      (L.separatedLinearIsometry n).toContinuousLinearMap x
  exact AddMonoidHom.extension_coe _ _ x

/-- The completed continuous-linear boundary realization preserves norm. -/
theorem completedLinearMap_norm
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ‖L.completedLinearMap n psi‖ = ‖psi‖ := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  change UniformSpace.Completion Pn.Separated at psi
  refine UniformSpace.Completion.induction_on psi
    (isClosed_eq (L.completedLinearMap n).continuous.norm continuous_norm) ?_
  intro x
  rw [L.completedLinearMap_coe]
  exact (L.separatedLinearIsometry n).norm_map x

/-- Canonical isometric realization of the completed finite Wilson OS Hilbert
space inside the actual shared-boundary `L²` space. -/
noncomputable def completedLinearIsometry
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N where
  toLinearMap := (L.completedLinearMap n).toLinearMap
  norm_map' := L.completedLinearMap_norm n

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
  change L.completedLinearMap n
      ((Pn.osClass F : Pn.Separated) : UniformSpace.Completion Pn.Separated) = _
  rw [L.completedLinearMap_coe]
  change L.separatedLinearIsometry n (SeparationQuotient.mk F) = _
  exact L.separatedLinearIsometry_mk n F

/-- The Hilbert adjoint of the completed boundary isometry is a left inverse on
its physical image: `J_n† J_n = I`. -/
theorem completedLinearIsometry_adjoint_apply
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    (((L.completedLinearIsometry n).toContinuousLinearMap)†)
        (L.completedLinearIsometry n psi) = psi := by
  apply ext_inner_left ℝ
  intro phi
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (L.completedLinearIsometry n).inner_map_map phi psi

/-- The canonical actual shared-boundary transfer at physical time `t`:
`K_{n,t} = J_n T_{n,t/2} J_n†`.

The half-time convention is the one used by the existing boundary-gap
interfaces.  The adjoint gives the canonical zero extension off the physical
boundary image. -/
noncomputable def canonicalBoundaryTransfer
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N := by
  let J := L.completedLinearIsometry n
  let Jadj :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n :=
    (J.toContinuousLinearMap)†
  exact J.toContinuousLinearMap.comp
    ((C.finiteOperator n (t / 2)).comp Jadj)

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
  let J := L.completedLinearIsometry n
  let Jadj :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n :=
    (J.toContinuousLinearMap)†
  change J (C.finiteOperator n (t / 2) (Jadj (J psi))) =
    J (C.finiteOperator n (t / 2) psi)
  have hLeft : Jadj (J psi) = psi := by
    dsimp [Jadj, J]
    exact L.completedLinearIsometry_adjoint_apply n psi
  rw [hLeft]

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

/-- Exact boundary-moment intertwining for every raw OS carrier vector. -/
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
      rw [finiteOperator_on_physicalState C n (t / 2) F]
    _ = physicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryMomentL2
        S D halfExtent N hN beta hbeta B hInvariant n
        (Tn.carrierTranslation (t / 2) F) := by
      rw [L.completedLinearIsometry_physicalState]

/-- The canonical boundary transfer is contractive on the entire boundary
`L²` space.  This is a structural `≤ 1` estimate only; it is deliberately not
a strict vacuum-sector contraction. -/
theorem canonicalBoundaryTransfer_norm_le
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ) (t : NNReal)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    ‖L.canonicalBoundaryTransfer C n t v‖ ≤ ‖v‖ := by
  let J := L.completedLinearIsometry n
  let Jadj :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
        PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n :=
    (J.toContinuousLinearMap)†
  have hJ : ‖J.toContinuousLinearMap‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound J.toContinuousLinearMap zero_le_one ?_
    intro psi
    simpa using (le_refl ‖psi‖)
  have hAdj : ‖Jadj‖ ≤ 1 := by
    dsimp [Jadj]
    simpa using hJ
  have hT : ‖C.finiteOperator n (t / 2)‖ ≤ 1 :=
    C.finiteOperator_opNorm_le n (t / 2)
  change ‖J (C.finiteOperator n (t / 2) (Jadj v))‖ ≤ ‖v‖
  rw [J.norm_map]
  calc
    ‖C.finiteOperator n (t / 2) (Jadj v)‖ ≤
        ‖C.finiteOperator n (t / 2)‖ * ‖Jadj v‖ :=
      (C.finiteOperator n (t / 2)).le_opNorm _
    _ ≤ 1 * ‖Jadj v‖ :=
      mul_le_mul_of_nonneg_right hT (norm_nonneg _)
    _ = ‖Jadj v‖ := one_mul _
    _ ≤ ‖Jadj‖ * ‖v‖ := Jadj.le_opNorm v
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
