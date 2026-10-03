import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2GramSchmidtPairPhysical
import MGAP4D.MathlibAnalytic.RealEuclideanFinThreeTwoFunctionalKernel
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSUNTwoModeFiniteOSPairTopTopScalarCriterion
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedCenteredPairScalarReplacement
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairUniformNonTopDecay
import Mathlib.Tactic

/-!
# Exact SU(2) three-mode physical non-top excitation

The post-H1-D5 route needs a finite vector that is simultaneously orthogonal to

* the actual finite OS vacuum pair, and
* the physical pair top mode,

without identifying those two directions.

PR #5077 supplies an infinite orthonormal family of explicit physical SU(2)
endpoint-pair modes.  PR #5078 supplies the rank-nullity fact that two real
linear functionals on R^3 have a common unit kernel vector.

This file joins those two ingredients.

For the first three physical pair modes we construct a canonical synthesis
linear isometry

  Syn_H : EuclideanSpace R (Fin 3) -> PairHaarL2(H, SU(2)).

At every finite scale, the vacuum and pair-top matrix coefficients become two
real linear functionals on the three-dimensional coefficient space.  Applying
#5078 theorem-generates a unit coefficient c_n annihilating both.  Its
synthesis x_n is therefore

* unit norm;
* in the completed physical pair carrier;
* exactly finite-vacuum centered;
* exactly orthogonal to the completed top-top block;
* hence in the completed physical pair non-top block;
* and therefore receives the existing scale-uniform q0^m estimate.

No H1-D5 compatibility, vacuum/top alignment, fidelity limit, or local
top-coefficient decay assumption appears.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance su2ThreeModeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ThreeModeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ThreeModeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ThreeModeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ThreeModeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ThreeModeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2ThreeModeSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2ThreeModeNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The first three theorem-generated SU(2) physical pair modes. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
    (H : ℕ) :
    Fin 3 → PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
  fun k =>
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
      H k.1

/-- Restricting the full #5077 family to the first three indices preserves
orthonormality. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_orthonormal
    (H : ℕ) :
    Orthonormal ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        H) := by
  let f : Fin 3 → ℕ := fun k => k.1
  have hf : Function.Injective f := by
    intro i j hij
    exact Fin.ext hij
  simpa [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode,
    f,
    Function.comp_def
  ] using
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_orthonormal
      H).comp f hf

/-- The linear map sending the standard Euclidean basis of R^3 to the first
three physical pair modes. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesisLinearMap
    (H : ℕ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
      H)

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesisLinearMap_basisFun
    (H : ℕ) (k : Fin 3) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesisLinearMap
        H
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        H k := by
  change
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        H))
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis k) =
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
      H k
  exact
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr_basis ℝ
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        H) k

/-- The first-three-mode synthesis is a linear isometry. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
    (H : ℕ) :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H 2 :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesisLinearMap
      H).isometryOfOrthonormal
    (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal
    (by
      simpa [Function.comp_def] using
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_orthonormal
          H)

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_basisFun
    (H : ℕ) (k : Fin 3) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        H
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        H k := by
  change
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesisLinearMap
        H
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        H k
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesisLinearMap_basisFun
      H k

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_norm
    (H : ℕ) (c : EuclideanSpace ℝ (Fin 3)) :
    ‖periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        H c‖ = ‖c‖ :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
    H).norm_map c

/-- Every finite three-mode synthesis remains in the completed physical pair
carrier by submodule linearity and #5077 modewise membership. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_mem_physicalPairCarrier
    (H : ℕ) (c : EuclideanSpace ℝ (Fin 3)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        H c ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2 := by
  rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr c]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro k hk
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_basisFun]
  exact
    Submodule.smul_mem
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).repr c k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_mem_physicalPairCarrier
        H k.1)

section FiniteScale

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {h2 : 0 < (2 : ℕ)}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 h2 beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- Vacuum matrix coefficient pulled back to the three-dimensional coefficient
space. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSU2ThreeModeVacuumFunctional
    (n : ℕ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  (innerSL ℝ
      (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := 2) (hN := h2)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)).toLinearMap.comp
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
      (halfExtent n)).toLinearMap

@[simp]
theorem physicalYangMillsVacuumNormalizedSU2ThreeModeVacuumFunctional_apply
    (n : ℕ) (c : EuclideanSpace ℝ (Fin 3)) :
    physicalYangMillsVacuumNormalizedSU2ThreeModeVacuumFunctional
        Q hInvariant n c =
      inner ℝ
        (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
          (S := S) (D := D) (halfExtent := halfExtent)
          (N := 2) (hN := h2)
          (beta := beta) (hbeta := hbeta)
          (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c) := by
  rfl

/-- Pair-top matrix coefficient pulled back to the same coefficient space. -/
noncomputable def
    physicalYangMillsVacuumNormalizedSU2ThreeModePairTopFunctional
    (n : ℕ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  (innerSL ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
        (halfExtent n) 2 h2 (beta n) (hbeta n))).toLinearMap.comp
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
      (halfExtent n)).toLinearMap

@[simp]
theorem physicalYangMillsVacuumNormalizedSU2ThreeModePairTopFunctional_apply
    (n : ℕ) (c : EuclideanSpace ℝ (Fin 3)) :
    physicalYangMillsVacuumNormalizedSU2ThreeModePairTopFunctional
        (halfExtent := halfExtent) (h2 := h2)
        (beta := beta) (hbeta := hbeta) n c =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          (halfExtent n) 2 h2 (beta n) (hbeta n))
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c) := by
  rfl

/-- At every finite scale there is a unit coefficient vector whose synthesized
physical pair is simultaneously vacuum-orthogonal and pair-top-orthogonal. -/
theorem
    physicalYangMillsVacuumNormalizedSU2_exists_unit_threeModeCoefficient_vacuum_pairTop_orthogonal
    (n : ℕ) :
    ∃ c : EuclideanSpace ℝ (Fin 3),
      ‖c‖ = 1 ∧
      inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := 2) (hN := h2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c) = 0 ∧
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) 2 h2 (beta n) (hbeta n))
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c) = 0 := by
  simpa using
    (realEuclideanFinThree_exists_unit_annihilating_two
      (physicalYangMillsVacuumNormalizedSU2ThreeModeVacuumFunctional
        Q hInvariant n)
      (physicalYangMillsVacuumNormalizedSU2ThreeModePairTopFunctional
        (halfExtent := halfExtent) (h2 := h2)
        (beta := beta) (hbeta := hbeta) n))

/-- The theorem-generated three-mode coefficient produces an exact unit
physical non-top excitation which is unchanged by finite vacuum centering. -/
theorem
    physicalYangMillsVacuumNormalizedSU2_exists_unit_threeModeExactPhysicalNonTopExcitation
    (n : ℕ) :
    ∃ c : EuclideanSpace ℝ (Fin 3),
      ‖c‖ = 1 ∧
      ‖periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c‖ = 1 ∧
      inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := 2) (hN := h2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c) = 0 ∧
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) 2 h2 (beta n) (hbeta n))
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c) = 0 ∧
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent n) 2 ∧
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
          (halfExtent n) 2 h2 (beta n) (hbeta n) ∧
      finiteVacuumCentered
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := 2) (hN := h2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c) =
        periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c := by
  obtain ⟨c, hcNorm, hcVac, hcTop⟩ :=
    physicalYangMillsVacuumNormalizedSU2_exists_unit_threeModeCoefficient_vacuum_pairTop_orthogonal
      Q hInvariant n
  let x :=
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
      (halfExtent n) c
  have hxNorm : ‖x‖ = 1 := by
    simpa [x] using
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_norm
        (halfExtent n) c).trans hcNorm
  have hxPhysical :
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2 := by
    simpa [x] using
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_mem_physicalPairCarrier
        (halfExtent n) c
  have hxTopOrth :
      x ∈
        (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure
          (halfExtent n) 2 h2 (beta n) (hbeta n))ᗮ := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairTopTopBlockClosure_orthogonal_mem_iff_pairTopMode_inner_eq_zero
        (halfExtent n) 2 h2 (beta n) (hbeta n) x).2
        (by simpa [x] using hcTop)
  have hxNonTop :
      x ∈ periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
        (halfExtent n) 2 h2 (beta n) (hbeta n) := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopClosure_eq_carrier_inf_topTopOrthogonal
        (halfExtent n) 2 h2 (beta n) (hbeta n)]
    exact ⟨hxPhysical, hxTopOrth⟩
  have hxCentered :
      finiteVacuumCentered
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := 2) (hN := h2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          x = x := by
    unfold finiteVacuumCentered
    rw [show
      inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := 2) (hN := h2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          x = 0 by
        simpa [x] using hcVac]
    simp
  exact
    ⟨c, hcNorm, by simpa [x] using hxNorm,
      hcVac, hcTop,
      by simpa [x] using hxPhysical,
      by simpa [x] using hxNonTop,
      by simpa [x] using hxCentered⟩

/-- The exact theorem-generated unit three-mode excitation receives the
existing scale-uniform q0^m decay directly on the full completed physical
pair non-top sector. -/
theorem
    physicalYangMillsVacuumNormalizedSU2_exists_unit_threeModeExactPhysicalNonTopExcitation_pow_norm_le_uniform_q0
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n : ℕ) :
    ∃ c : EuclideanSpace ℝ (Fin 3),
      ‖c‖ = 1 ∧
      ‖periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c‖ = 1 ∧
      inner ℝ
          (physicalYangMillsSUNTwoModeExplicitOSVacuumBoundaryPairL2
            (S := S) (D := D) (halfExtent := halfExtent)
            (N := 2) (hN := h2)
            (beta := beta) (hbeta := hbeta)
            (Q := Q.vacuumNormalized) (hInvariant := hInvariant) n)
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c) = 0 ∧
      inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
            (halfExtent n) 2 h2 (beta n) (hbeta n))
          (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
            (halfExtent n) c) = 0 ∧
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n) c ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure
          (halfExtent n) 2 h2 (beta n) (hbeta n) ∧
      (∀ m : ℕ,
        ‖(periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
            (halfExtent n) 2 h2 (beta n) (hbeta n) ^ m)
            (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
              (halfExtent n) c)‖ ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ m) := by
  obtain ⟨c, hcNorm, hxNorm, hcVac, hcTop, hxPhysical, hxNonTop, hxCentered⟩ :=
    physicalYangMillsVacuumNormalizedSU2_exists_unit_threeModeExactPhysicalNonTopExcitation
      Q hInvariant n
  refine ⟨c, hcNorm, hxNorm, hcVac, hcTop, hxNonTop, ?_⟩
  intro m
  have hdecay :=
    periodicHypercubicEvenSpecialUnitary_uniformPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
      halfExtent 2 h2 beta hbeta s hs hcut n m
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
        (halfExtent n) c)
      hxNonTop
  simpa [hxNorm] using hdecay

end FiniteScale

end

end MathlibAnalytic
end MGAP4D
