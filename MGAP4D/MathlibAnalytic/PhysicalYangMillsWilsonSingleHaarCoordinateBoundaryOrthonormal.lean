import MGAP4D.MathlibAnalytic.FiniteProductProbabilityCoordinateL2Orthonormal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryHaarProjectiveCylinderOrthonormal

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance singleHaarCoordinateTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance singleHaarCoordinateCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance singleHaarCoordinateSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance singleHaarCoordinateMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance singleHaarCoordinateBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Real `L²` of one normalized Haar-distributed `SU(N)` variable. -/
abbrev SpecialUnitaryNormalizedHaarL2 (N : ℕ) :=
  Lp ℝ 2 (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- A canonical spatial edge on the primary reflection-fixed time slice.

The zero vertex has source time zero and axis `1` is spatial, so the existing
edge-side classification theorem places this link in the fixed boundary
sector for every half-extent `H`. -/
noncomputable def periodicHypercubicEvenPrimaryBoundarySpatialEdge
    (H : ℕ) :
    (periodicHypercubicEvenEdgeOrbitPartition H).FixedEdge := by
  refine ⟨
    ((0 : PeriodicHypercubicEvenVertex H), (1 : PeriodicHypercubicAxis)), ?_⟩
  change periodicHypercubicEvenEdgeSide H
      ((0 : PeriodicHypercubicEvenVertex H), (1 : PeriodicHypercubicAxis)) =
    ReflectionEdgeSide.fixed
  apply periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
  · decide
  · simp

/-- Pull one normalized-Haar `SU(N)` `L²` coordinate into the full reflection
boundary product Haar `L²`, using the canonical primary spatial boundary edge.
-/
noncomputable def periodicHypercubicEvenPrimaryBoundaryCoordinateL2Pullback
    (H N : ℕ) :
    SpecialUnitaryNormalizedHaarL2 N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  let μ : P.FixedEdge →
      Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ => normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  change Lp ℝ 2 (normalizedCompactHaar
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) →ₗᵢ[ℝ]
    Lp ℝ 2 (Measure.pi μ)
  exact finiteProductProbabilityCoordinateL2Pullback μ
    (periodicHypercubicEvenPrimaryBoundarySpatialEdge H)

/-- Single-coordinate normalized-Haar orthonormality is preserved after
pullback to the full finite boundary product Haar space. -/
theorem periodicHypercubicEvenPrimaryBoundaryCoordinateL2Pullback_orthonormal
    (H N : ℕ)
    {κ : Type*}
    (v : κ → SpecialUnitaryNormalizedHaarL2 N)
    (hv : Orthonormal ℝ v) :
    Orthonormal ℝ
      ((periodicHypercubicEvenPrimaryBoundaryCoordinateL2Pullback H N) ∘ v) :=
  hv.comp_linearIsometry
    (periodicHypercubicEvenPrimaryBoundaryCoordinateL2Pullback H N)

/-- A single-`SU(N)`-Haar-coordinate realization of the boundary-Haar
orthonormal strictness package.

For each finite selected cylinder family, the only orthonormality input now
lives on one normalized-Haar `SU(N)` variable.  Its canonical boundary
coordinate pullback is then required to realize the boundary vectors used by
#1609 after density correction and projective readout.

This localizes the remaining compact-group statement to a single compact group:
construct a gauge-invariant class-function/character family orthonormal in
`L²(SU(N), normalized Haar)` and identify its pulled-back modes with the
selected Wilson cylinder observables. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderSingleHaarCoordinateOrthonormalData
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)) where
  observable : ℕ → D.positiveTimeSubalgebra.toSubmodule
  cylinderIndex : ℕ → Finset EuclideanFourSpace
  cylinderVector : ∀ k,
    Lp ℝ 2 (F.finiteMarginal (cylinderIndex k))
  supportEventually : ∀ k,
    ∀ᶠ n in atTop, cylinderIndex k ⊆ R.marginalIndex n
  finiteImage_eq_transition : ∀ k n
      (h : cylinderIndex k ⊆ R.marginalIndex n),
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    R.finiteOSMarginalLinearIsometry hInvariant n
        (Pn.physicalState
          (Pn.positiveTimeSubmoduleCarrierLinearMap (observable k))) =
      EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
        (F := F) h (cylinderVector k)
  finiteSingleHaarCoordinateOrthonormalRealization : ∀ s : Finset ℕ,
    ∃ n : ℕ,
      ∃ hCommon : s.biUnion cylinderIndex ⊆ R.marginalIndex n,
        ∃ haarVector : s → SpecialUnitaryNormalizedHaarL2 N,
          Orthonormal ℝ haarVector ∧
          ∀ i : s,
            R.boundaryHaarProjectiveL2Isometry n
                (periodicHypercubicEvenPrimaryBoundaryCoordinateL2Pullback
                  (halfExtent n) N (haarVector i)) =
              EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
                (F := F)
                ((Finset.subset_biUnion_of_mem cylinderIndex i.property).trans hCommon)
                (cylinderVector (i : ℕ))

namespace PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderSingleHaarCoordinateOrthonormalData

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- Forget only the single-coordinate realization layer and recover exactly the
boundary-Haar orthonormal datum integrated in #1609. -/
noncomputable def toBoundaryHaarOrthonormalData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderSingleHaarCoordinateOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant where
  observable := C.observable
  cylinderIndex := C.cylinderIndex
  cylinderVector := C.cylinderVector
  supportEventually := C.supportEventually
  finiteImage_eq_transition := C.finiteImage_eq_transition
  finiteBoundaryHaarOrthonormalRealization := by
    intro s
    rcases C.finiteSingleHaarCoordinateOrthonormalRealization s with
      ⟨n, hCommon, haarVector, hHaar, hRealize⟩
    refine ⟨n, hCommon,
      (periodicHypercubicEvenPrimaryBoundaryCoordinateL2Pullback
        (halfExtent n) N) ∘ haarVector, ?_, ?_⟩
    · exact periodicHypercubicEvenPrimaryBoundaryCoordinateL2Pullback_orthonormal
        (halfExtent n) N haarVector hHaar
    · intro i
      exact hRealize i

/-- Single normalized-Haar `SU(N)` coordinate orthonormal realization
therefore theorem-generates the exact strict continuum finite-Gram carrier. -/
noncomputable def toFiniteOSGramPosDefPhysicalCarrierData
    (C : PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderSingleHaarCoordinateOrthonormalData
      S D halfExtent N hN beta hbeta Q F R L hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCommonProductFiniteOSGramPosDefPhysicalCarrierData
      halfExtent N hN beta hbeta
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant)
      (physical_yang_mills_evenPeriodicWilsonOS_continuum_preHilbertData_isNormalized
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant) :=
  PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderBoundaryHaarOrthonormalData.toFiniteOSGramPosDefPhysicalCarrierData
    C.toBoundaryHaarOrthonormalData

end PhysicalYangMillsEvenPeriodicWilsonOSFiniteProjectiveCylinderSingleHaarCoordinateOrthonormalData

end

end MathlibAnalytic
end MGAP4D
