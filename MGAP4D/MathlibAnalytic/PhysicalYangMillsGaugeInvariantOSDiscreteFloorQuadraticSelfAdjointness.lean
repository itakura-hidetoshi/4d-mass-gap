import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDiscreteFloorSelfAdjointness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSQuadraticStrongContinuity

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
namespace PositiveTimeObservableContractionSemigroup
namespace ContinuumTimeReflectionBridge

private theorem physicalTranslate_nnreal_continuous
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {A : E₀.PhysicalDiscreteTemporalAction}
    (J : A.JointContinuity) (X : E₀.PhysicalConfiguration) :
    Continuous (fun t : NNReal => A.physicalTranslate (t : ℝ) X) := by
  have hPair : Continuous (fun t : NNReal => ((t : ℝ), X)) := by
    fun_prop
  change Continuous (A.jointTranslate ∘ fun t : NNReal => ((t : ℝ), X))
  exact J.jointTranslate_continuous.comp hPair

private theorem osQuadraticDifferenceIntegrand_eq_ofDiscreteFloor
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T)
    (t : NNReal) (F : D.positiveTimeSubalgebra)
    (X : (G.toSymmetryLimit L).Configuration) :
    T.osQuadraticDifferenceIntegrand t F X =
      (F.1.1 (A.physicalTranslate (t : ℝ) (H.configurationReflection X)) -
          F.1.1 (H.configurationReflection X)) *
        (F.1.1 (A.physicalTranslate (t : ℝ) X) - F.1.1 X) := by
  change
    (((D.reflection
          ((T.translate t F :
              physicalYangMillsGaugeInvariantObservableSubalgebra
                (G.toSymmetryLimit L)) -
            (F : physicalYangMillsGaugeInvariantObservableSubalgebra
              (G.toSymmetryLimit L))) *
        ((T.translate t F :
              physicalYangMillsGaugeInvariantObservableSubalgebra
                (G.toSymmetryLimit L)) -
            (F : physicalYangMillsGaugeInvariantObservableSubalgebra
              (G.toSymmetryLimit L))) :
      physicalYangMillsGaugeInvariantObservableSubalgebra
        (G.toSymmetryLimit L)) :
      BoundedContinuousFunction (G.toSymmetryLimit L).Configuration ℝ) X) = _
  rw [H.reflection_realization]
  simp only [← H.positive_restriction t F]
  rfl

private theorem osQuadraticDifferenceIntegrand_continuousAt_zero_ofDiscreteFloor
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (J : A.JointContinuity)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T)
    (F : D.positiveTimeSubalgebra)
    (X : (G.toSymmetryLimit L).Configuration) :
    ContinuousAt (fun t : NNReal => T.osQuadraticDifferenceIntegrand t F X) 0 := by
  rw [osQuadraticDifferenceIntegrand_eq_ofDiscreteFloor C L H]
  have hReflectionTranslate :
      Continuous
        (fun t : NNReal =>
          F.1.1
            (A.physicalTranslate (t : ℝ) (H.configurationReflection X))) :=
    F.1.1.continuous.comp
      (physicalTranslate_nnreal_continuous J (H.configurationReflection X))
  have hTranslate :
      Continuous
        (fun t : NNReal => F.1.1 (A.physicalTranslate (t : ℝ) X)) :=
    F.1.1.continuous.comp (physicalTranslate_nnreal_continuous J X)
  exact
    ((hReflectionTranslate.sub continuous_const).mul
      (hTranslate.sub continuous_const)).continuousAt

private theorem osQuadraticDifferenceIntegrand_norm_le_ofDiscreteFloor
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T)
    (t : NNReal) (F : D.positiveTimeSubalgebra)
    (X : (G.toSymmetryLimit L).Configuration) :
    ‖T.osQuadraticDifferenceIntegrand t F X‖ ≤
      (2 * ‖F.1.1‖) ^ 2 := by
  rw [osQuadraticDifferenceIntegrand_eq_ofDiscreteFloor C L H, norm_mul]
  have hReflection :
      ‖F.1.1 (A.physicalTranslate (t : ℝ) (H.configurationReflection X)) -
          F.1.1 (H.configurationReflection X)‖ ≤
        2 * ‖F.1.1‖ := by
    simpa only [dist_eq_norm] using
      F.1.1.dist_le_two_norm
        (A.physicalTranslate (t : ℝ) (H.configurationReflection X))
        (H.configurationReflection X)
  have hDirect :
      ‖F.1.1 (A.physicalTranslate (t : ℝ) X) - F.1.1 X‖ ≤
        2 * ‖F.1.1‖ := by
    simpa only [dist_eq_norm] using
      F.1.1.dist_le_two_norm (A.physicalTranslate (t : ℝ) X) X
  have hProduct := mul_le_mul hReflection hDirect (norm_nonneg _) (by positivity)
  simpa only [pow_two] using hProduct

/-- Existing joint temporal continuity and bounded-continuous observables provide
the exact pointwise input for dominated convergence.  The reflected quadratic
integrand is uniformly bounded by the constant `(2 * ‖F‖∞)^2`. -/
noncomputable def osQuadraticUniformBoundContinuityAtZero_ofDiscreteTemporalAction
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (J : A.JointContinuity)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T) :
    T.OSQuadraticUniformBoundContinuityAtZero where
  omega_eq_continuumState := H.omega_eq_continuumState
  bound := fun F => (2 * ‖F.1.1‖) ^ 2
  integrand_bound := fun F t X =>
    osQuadraticDifferenceIntegrand_norm_le_ofDiscreteFloor C L H t F X
  integrand_tendsto := fun F X =>
    osQuadraticDifferenceIntegrand_continuousAt_zero_ofDiscreteFloor C J L H F X

/-- The uniform pointwise estimate is promoted to the complete measure-theoretic
dominated-convergence package by the continuum probability law. -/
noncomputable def osQuadraticDominatedConvergenceAtZero_ofDiscreteTemporalAction
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (J : A.JointContinuity)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T) :
    T.OSQuadraticDominatedConvergenceAtZero :=
  (osQuadraticUniformBoundContinuityAtZero_ofDiscreteTemporalAction C J L H).toOSQuadraticDominatedConvergenceAtZero

/-- The scalar OS quadratic continuity previously left as an analytic input is
generated from the existing floor-time joint continuity and the boundedness of
physical observables. -/
noncomputable def osQuadraticContinuityAtZero_ofDiscreteTemporalAction
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A)
    (J : A.JointContinuity)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T) :
    T.OSQuadraticContinuityAtZero :=
  (osQuadraticUniformBoundContinuityAtZero_ofDiscreteTemporalAction C J L H).toOSQuadraticContinuityAtZero

/-- Exact finite integer temporal translations, floor dense-time approximation,
joint continuity, continuum reflection compatibility, and continuity at zero of
the scalar OS quadratic difference imply self-adjointness of the graph-closed OS
Hamiltonian.

The Hilbert-valued strong-continuity input is generated internally from the
quadratic expectation. -/
theorem closedRightHamiltonian_isSelfAdjoint_ofDiscreteTemporalActionOfFloor_ofOSQuadraticContinuity
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A) (J : A.JointContinuity)
    (latticeTime_eq : ∀ n k,
      A.latticeTime n k = (k : ℝ) * E₀.latticeSpacing n)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T)
    (hQuadratic : T.OSQuadraticContinuityAtZero) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T hQuadratic.toStrongContinuityOnObservableStates).closedRightHamiltonian := by
  exact closedRightHamiltonian_isSelfAdjoint_ofDiscreteTemporalActionOfFloor
    C J latticeTime_eq L H hQuadratic.toStrongContinuityOnObservableStates

/-- The complete floor-time route no longer assumes Hilbert-valued strong
continuity or scalar OS quadratic continuity.  Both are generated from joint
configuration-time continuity, bounded continuous observables, and dominated
convergence. -/
theorem closedRightHamiltonian_isSelfAdjoint_ofDiscreteTemporalActionOfFloor_ofQuadraticDCT
    {E₀ : ContinuousCompactOrientedGaugeWilsonPhysicalEmbedding}
    {G : E₀.PhysicalGaugeAction} {A : E₀.PhysicalDiscreteTemporalAction}
    (C : E₀.GaugeDiscreteTemporalCompatibility G A) (J : A.JointContinuity)
    (latticeTime_eq : ∀ n k,
      A.latticeTime n k = (k : ℝ) * E₀.latticeSpacing n)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit
      E₀.toLatticeEmbedding)
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData (G.toSymmetryLimit L)}
    {P : D.OSPreHilbertData}
    {T : P.PositiveTimeObservableContractionSemigroup}
    (H : DiscreteFloorCompatibility C L T) :
    IsSelfAdjoint
      (StrongContinuityOnObservableStates.toStronglyContinuousPhysicalSemigroup
        T
        (osQuadraticContinuityAtZero_ofDiscreteTemporalAction C J L H).toStrongContinuityOnObservableStates).closedRightHamiltonian := by
  exact
    closedRightHamiltonian_isSelfAdjoint_ofDiscreteTemporalActionOfFloor_ofOSQuadraticContinuity
      C J latticeTime_eq L H
      (osQuadraticContinuityAtZero_ofDiscreteTemporalAction C J L H)

end ContinuumTimeReflectionBridge
end PositiveTimeObservableContractionSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
