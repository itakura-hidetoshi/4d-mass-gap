import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeCoefficientCompactness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadout
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryL2SpatialSlicePair
import Mathlib.Tactic

/-!
# Projective strong limit of the exact SU(2) three-mode excitation

PR #5081 constructs, at every finite scale, an exact unit physical pair
excitation in the first three SU(2) Wilson-energy Gram--Schmidt modes which is
simultaneously orthogonal to the actual finite OS vacuum and to the physical
pair-top direction.  PR #5082 chooses one such coefficient at every scale and
extracts a strictly increasing subsequence converging on the unit sphere of
R^3.

This file transports that coefficient compactness to the single projective
continuum L2 carrier.

The transport is the canonical chain

  ordered pair Haar L2
    -> boundary Haar L2
    -> interacting projective finite marginal L2
    -> projective-limit continuum L2.

All arrows are theorem-generated linear isometries.

For the first three Wilson Gram--Schmidt modes, continuum coherence implies
that this finite-scale synthesis is eventually *exactly equal* to a fixed
continuum synthesis.  The latter is again a linear isometry because its three
continuum modes are orthonormal.

Consequently the selected exact finite excitations admit a subsequence whose
canonical projective images converge strongly to a continuum vector of norm
one.  In particular the continuum initial excitation is nonzero.

No H1-D5 compatibility, vacuum/top alignment, fidelity limit, or top-direction
convergence is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2ThreeModeProjectiveLimitTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2ThreeModeProjectiveLimitCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2ThreeModeProjectiveLimitSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2ThreeModeProjectiveLimitMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2ThreeModeProjectiveLimitBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2ThreeModeProjectiveLimitSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2ThreeModeProjectiveLimitSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance su2ThreeModeProjectiveLimitNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section ProjectiveStrongLimit

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))

/-- Canonical isometric embedding of the finite ordered pair-Haar carrier into
one common projective-limit continuum L2 carrier. -/
noncomputable def physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2 →ₗᵢ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (L.finiteMarginalL2Pullback (R.marginalIndex n)).comp
    ((R.boundaryHaarProjectiveL2Isometry n).comp
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        (halfExtent n) 2))

@[simp]
theorem physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_norm
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2) :
    ‖physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n x‖ = ‖x‖ :=
  (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
    Q R L n).norm_map x

/-- On each theorem-generated Gram--Schmidt pair mode, the canonical pair
embedding is exactly the continuum pullback of the corresponding finite
projective mode. -/
@[simp]
theorem physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_gramSchmidtPairMode
    (n k : ℕ) :
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
          (halfExtent n) k) =
      L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k) := by
  unfold physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
  change
    L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.boundaryHaarProjectiveL2Isometry n
          (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
            (halfExtent n) 2
            (periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry
              (halfExtent n) 2
              (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
                (halfExtent n) k)))) =
      L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k)
  rw [periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundary_leftInverse]
  rfl

/-- Finite-scale first-three-mode synthesis after the full canonical embedding
into the common projective-limit continuum carrier. -/
noncomputable def physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
    (n : ℕ) :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
    Q R L n).comp
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
      (halfExtent n))

@[simp]
theorem physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis_basisFun
    (n : ℕ) (k : Fin 3) :
    physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
        Q R L n
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      L.finiteMarginalL2Pullback (R.marginalIndex n)
        (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode
          n k.1) := by
  change
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
        Q R L n
        (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis
          (halfExtent n)
          (EuclideanSpace.basisFun (Fin 3) ℝ k)) =
      _
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeSynthesis_basisFun]
  unfold
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
  exact
    physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding_gramSchmidtPairMode
      Q R L n k.1

/-- The fixed first three canonical continuum Gram--Schmidt modes. -/
noncomputable def physicalYangMillsSU2ThreeModeContinuumMode
    (k : Fin 3) :
    Lp ℝ 2 L.continuumMeasure :=
  R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode L k.1

/-- Continuum coherence plus finite-marginal orthonormality makes the first
three canonical continuum modes orthonormal. -/
theorem physicalYangMillsSU2ThreeModeContinuumMode_orthonormal
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    Orthonormal ℝ
      (physicalYangMillsSU2ThreeModeContinuumMode
        Q R L) := by
  have h0 := C.marginalSupportEventually 0
  have h1 := C.marginalSupportEventually 1
  have h2 := C.marginalSupportEventually 2
  have hall :
      ∀ᶠ n in atTop,
        R.marginalIndex 0 ⊆ R.marginalIndex n ∧
        R.marginalIndex 1 ⊆ R.marginalIndex n ∧
        R.marginalIndex 2 ⊆ R.marginalIndex n := by
    filter_upwards [h0, h1, h2] with n hn0 hn1 hn2
    exact ⟨hn0, hn1, hn2⟩
  obtain ⟨n, hn0, hn1, hn2⟩ := hall.exists
  let v : Fin 3 → Lp ℝ 2 (F.finiteMarginal (R.marginalIndex n)) :=
    fun k =>
      R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode n k.1
  have hv : Orthonormal ℝ v := by
    let f : Fin 3 → ℕ := fun k => k.1
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.ext hij
    simpa [v, f, Function.comp_def] using
      (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode_orthonormal n).comp
        f hf
  have hvPull :
      Orthonormal ℝ
        ((L.finiteMarginalL2Pullback (R.marginalIndex n)) ∘ v) :=
    hv.comp_linearIsometry
      (L.finiteMarginalL2Pullback (R.marginalIndex n))
  have hfamily :
      ((L.finiteMarginalL2Pullback (R.marginalIndex n)) ∘ v) =
        physicalYangMillsSU2ThreeModeContinuumMode
          Q R L := by
    funext k
    change
      L.finiteMarginalL2Pullback (R.marginalIndex n)
          (R.primarySpatialPlaquetteWilsonEnergyGramSchmidtProjectiveL2Mode
            n k.1) =
        R.primarySpatialPlaquetteWilsonEnergyGramSchmidtContinuumL2Mode
          L k.1
    fin_cases k
    · exact C.primaryPlaquetteGramSchmidtMode_continuum 0 n hn0
    · exact C.primaryPlaquetteGramSchmidtMode_continuum 1 n hn1
    · exact C.primaryPlaquetteGramSchmidtMode_continuum 2 n hn2
  rw [hfamily] at hvPull
  exact hvPull

/-- Linear map sending the standard basis of R^3 to the fixed continuum
Gram--Schmidt modes. -/
noncomputable def physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap
    :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ
    (physicalYangMillsSU2ThreeModeContinuumMode
      Q R L)

@[simp]
theorem physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap_basisFun
    (k : Fin 3) :
    physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap
        Q R L
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      physicalYangMillsSU2ThreeModeContinuumMode
        Q R L k := by
  change
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr ℝ
      (physicalYangMillsSU2ThreeModeContinuumMode
        Q R L))
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis k) =
    physicalYangMillsSU2ThreeModeContinuumMode
      Q R L k
  exact
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.constr_basis ℝ
      (physicalYangMillsSU2ThreeModeContinuumMode
        Q R L) k

private theorem su2ThreeModeProjectiveLimitEuclideanBasis_orthonormal :
    Orthonormal ℝ
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis :
        Fin 3 → EuclideanSpace ℝ (Fin 3)) := by
  simpa only [OrthonormalBasis.coe_toBasis] using
    (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal

private theorem physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap_comp_basis_orthonormal
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    Orthonormal ℝ
      (physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap
          Q R L ∘
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis :
          Fin 3 → EuclideanSpace ℝ (Fin 3))) := by
  have hfun :
      (physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap
          Q R L ∘
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis :
          Fin 3 → EuclideanSpace ℝ (Fin 3))) =
        physicalYangMillsSU2ThreeModeContinuumMode
          Q R L := by
    funext k
    exact
      physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap_basisFun
        Q R L k
  rw [hfun]
  exact
    physicalYangMillsSU2ThreeModeContinuumMode_orthonormal
      Q R L hInvariant C

/-- The fixed continuum first-three-mode synthesis is a linear isometry. -/
noncomputable def physicalYangMillsSU2ThreeModeContinuumSynthesis
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  LinearMap.isometryOfOrthonormal
    (physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap
      Q R L)
    (v := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)
    su2ThreeModeProjectiveLimitEuclideanBasis_orthonormal
    (physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap_comp_basis_orthonormal
      Q R L hInvariant C)

@[simp]
theorem physicalYangMillsSU2ThreeModeContinuumSynthesis_basisFun
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (k : Fin 3) :
    physicalYangMillsSU2ThreeModeContinuumSynthesis
        Q R L hInvariant C
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      physicalYangMillsSU2ThreeModeContinuumMode
        Q R L k := by
  change
    physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap
        Q R L
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      physicalYangMillsSU2ThreeModeContinuumMode
        Q R L k
  exact
    physicalYangMillsSU2ThreeModeContinuumSynthesisLinearMap_basisFun
      Q R L k

@[simp]
theorem physicalYangMillsSU2ThreeModeContinuumSynthesis_norm
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant)
    (c : EuclideanSpace ℝ (Fin 3)) :
    ‖physicalYangMillsSU2ThreeModeContinuumSynthesis
        Q R L hInvariant C c‖ = ‖c‖ :=
  (physicalYangMillsSU2ThreeModeContinuumSynthesis
    Q R L hInvariant C).norm_map c

/-- Once all three source cylinder supports are contained in the selected
finite marginal, finite and fixed continuum three-mode syntheses agree exactly.
Hence the equality holds eventually in scale. -/
theorem physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis_eq_eventually
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ∀ᶠ n in atTop,
      ∀ c : EuclideanSpace ℝ (Fin 3),
        physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
            Q R L n c =
          physicalYangMillsSU2ThreeModeContinuumSynthesis
            Q R L hInvariant C c := by
  filter_upwards
    [C.marginalSupportEventually 0,
     C.marginalSupportEventually 1,
     C.marginalSupportEventually 2] with n hn0 hn1 hn2
  intro c
  rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr c]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [
    physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis_basisFun,
    physicalYangMillsSU2ThreeModeContinuumSynthesis_basisFun]
  unfold physicalYangMillsSU2ThreeModeContinuumMode
  fin_cases k
  · rw [C.primaryPlaquetteGramSchmidtMode_continuum 0 n hn0]
  · rw [C.primaryPlaquetteGramSchmidtMode_continuum 1 n hn1]
  · rw [C.primaryPlaquetteGramSchmidtMode_continuum 2 n hn2]

/-- The selected exact finite physical non-top excitations admit a subsequence
whose canonical projective images converge strongly to a unit continuum
excitation.  This closes the nonzero initial-vector part of the projective
continuum route. -/
theorem
    physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice_exists_projective_strong_limit
    (C :
      PhysicalYangMillsEvenPeriodicWilsonOSSU2PrimaryPlaquetteGramSchmidtContinuumCoherentReadoutData
        S D halfExtent beta hbeta Q F R L hInvariant) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ cInf : EuclideanSpace ℝ (Fin 3),
        ‖cInf‖ = 1 ∧
        Tendsto
          (fun j =>
            physicalYangMillsSU2PairHaarProjectiveContinuumEmbedding
              Q R L (phi j)
              (physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice
                Q hInvariant (phi j)))
          atTop
          (𝓝
            (physicalYangMillsSU2ThreeModeContinuumSynthesis
              Q R L hInvariant C cInf)) ∧
        ‖physicalYangMillsSU2ThreeModeContinuumSynthesis
            Q R L hInvariant C cInf‖ = 1 := by
  obtain ⟨phi, hphi, cInf, hcInf, hcTendsto⟩ :=
    physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice_exists_strictMono_tendsto
      Q hInvariant
  refine ⟨phi, hphi, cInf, hcInf, ?_, ?_⟩
  · have hFixed :
        Tendsto
          (fun j =>
            physicalYangMillsSU2ThreeModeContinuumSynthesis
              Q R L hInvariant C
              (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
                Q hInvariant (phi j)))
          atTop
          (𝓝
            (physicalYangMillsSU2ThreeModeContinuumSynthesis
              Q R L hInvariant C cInf)) := by
      have hMap :=
        ((physicalYangMillsSU2ThreeModeContinuumSynthesis
          Q R L hInvariant C).continuous.tendsto cInf).comp hcTendsto
      simpa [Function.comp_def] using hMap
    have hAlong :
        ∀ᶠ j in atTop,
          physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis
              Q R L (phi j)
              (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
                Q hInvariant (phi j)) =
            physicalYangMillsSU2ThreeModeContinuumSynthesis
              Q R L hInvariant C
              (physicalYangMillsVacuumNormalizedSU2ThreeModeCoefficientChoice
                Q hInvariant (phi j)) := by
      have hEvent :=
        hphi.tendsto_atTop.eventually
          (physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis_eq_eventually
            Q R L hInvariant C)
      filter_upwards [hEvent] with j hj
      exact hj _
    apply hFixed.congr'
    filter_upwards [hAlong] with j hj
    simpa [
      physicalYangMillsSU2ThreeModeFiniteProjectiveContinuumSynthesis,
      physicalYangMillsVacuumNormalizedSU2ThreeModeExcitationChoice,
      Function.comp_def
    ] using hj.symm
  · exact
      (physicalYangMillsSU2ThreeModeContinuumSynthesis_norm
        Q R L hInvariant C cInf).trans hcInf

end ProjectiveStrongLimit

end

end MathlibAnalytic
end MGAP4D
