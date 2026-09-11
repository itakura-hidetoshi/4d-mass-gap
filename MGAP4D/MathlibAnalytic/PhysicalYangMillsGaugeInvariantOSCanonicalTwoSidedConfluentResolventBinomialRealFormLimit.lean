import MGAP4D.MathlibAnalytic.ContinuousLinearMapTwoSidedConfluentResolventBinomialNormalForm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalTwoSidedConfluentResolventJetRealFormLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap
open StandardRealHilbertComplexification

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The finite-time closed binomial normal form for positive multiplicities at
two distinct below-half-mass resolvent nodes. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalForm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (m n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.twoSidedConfluentResolventBinomialNormalForm
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau sigma.property)
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau rho.property)
    (sigma.1 - rho.1)⁻¹ m n

/-- The corresponding continuum closed binomial normal form. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventTwoSidedConfluentBinomialNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (m n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.twoSidedConfluentResolventBinomialNormalForm
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf sigma.property)
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf rho.property)
    (sigma.1 - rho.1)⁻¹ m n

/-- At finite time, the recursive two-sided confluent jet with positive
multiplicities is exactly its closed binomial normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentJet_succ_succ_eq_binomialNormalForm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (m n : ℕ) :
    G.admissibleRescaledDefectResolventTwoSidedConfluentJet
        hInnerSymmetric tau sigma rho (m + 1) (n + 1) =
      G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalForm
        hInnerSymmetric tau sigma rho m n := by
  exact
    ContinuousLinearMap.twoSidedConfluentResolventJetNormalForm_succ_succ_eq_binomialNormalForm
      (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)
      (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau rho.property)
      sigma.1 rho.1 m n

/-- In the continuum, the recursive two-sided confluent jet with positive
multiplicities is exactly the same closed binomial normal form. -/
theorem VacuumSemigroupGapSlope.continuumResolventTwoSidedConfluentJet_succ_succ_eq_binomialNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (m n : ℕ) :
    G.continuumResolventTwoSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho (m + 1) (n + 1) =
      G.continuumResolventTwoSidedConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf sigma rho m n := by
  exact
    ContinuousLinearMap.twoSidedConfluentResolventJetNormalForm_succ_succ_eq_binomialNormalForm
      (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)
      (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf rho.property)
      sigma.1 rho.1 m n

/-- At finite time, the positive two-block mixed resolvent product has the
closed finite binomial partial-fraction expansion. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_pow_succ_mul_pow_succ_eq_twoSidedConfluentBinomialNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property) ^ (m + 1) *
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau rho.property) ^ (n + 1) =
      G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalForm
        hInnerSymmetric tau sigma rho m n := by
  apply
    ContinuousLinearMap.pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
  · exact hne
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau sigma.property rho.property

/-- The continuum positive two-block mixed resolvent product has the same closed
finite binomial partial-fraction expansion. -/
theorem VacuumSemigroupGapSlope.continuumResolvent_pow_succ_mul_pow_succ_eq_twoSidedConfluentBinomialNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property) ^ (m + 1) *
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf rho.property) ^ (n + 1) =
      G.continuumResolventTwoSidedConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf sigma rho m n := by
  apply
    ContinuousLinearMap.pow_succ_mul_pow_succ_eq_twoSidedConfluentResolventBinomialNormalForm
  · exact hne
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf sigma.property rho.property

/-- Closed binomial normal forms converge pointwise strongly after canonical
diagonal complexification on the full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalForm
            hInnerSymmetric tau sigma rho m n) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventTwoSidedConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho m n) z)) := by
  simpa only [
    G.admissibleRescaledDefectResolventTwoSidedConfluentJet_succ_succ_eq_binomialNormalForm,
    G.continuumResolventTwoSidedConfluentJet_succ_succ_eq_binomialNormalForm] using
    G.admissibleRescaledDefectResolventTwoSidedConfluentJetDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf sigma rho hne (m + 1) (n + 1) z

/-- The continuum closed binomial normal form remains in the diagonal real-form
star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventTwoSidedConfluentBinomialNormalFormDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    diagonalComplexification
        (G.continuumResolventTwoSidedConfluentBinomialNormalForm
          T hP hInnerSymmetric hSelf sigma rho m n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [← G.continuumResolventTwoSidedConfluentJet_succ_succ_eq_binomialNormalForm
    T hP hInnerSymmetric hSelf sigma rho m n]
  exact
    G.continuumResolventTwoSidedConfluentJetDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf sigma rho hne (m + 1) (n + 1)

/-- The bounded real operator underlying the complex strong limit of a closed
binomial normal form exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalFormDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventTwoSidedConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho m n) := by
  rw [← G.continuumResolventTwoSidedConfluentJet_succ_succ_eq_binomialNormalForm
    T hP hInnerSymmetric hSelf sigma rho m n]
  exact
    G.admissibleRescaledDefectResolventTwoSidedConfluentJetDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf sigma rho hne (m + 1) (n + 1)

/-- Any bounded real operator producing the same complex pointwise strong limit
is exactly the continuum closed binomial normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalForm_real_limit_eq_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalForm
              hInnerSymmetric tau sigma rho m n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventTwoSidedConfluentBinomialNormalForm
      T hP hInnerSymmetric hSelf sigma rho m n := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventTwoSidedConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho m n) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho hne m n z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual OS real-form strong-limit package for the closed finite binomial
partial-fraction expansion at two distinct resolvent nodes. -/
theorem VacuumSemigroupGapSlope.canonicalTwoSidedConfluentResolventBinomialRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalForm
              hInnerSymmetric tau sigma rho m n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventTwoSidedConfluentBinomialNormalForm
              T hP hInnerSymmetric hSelf sigma rho m n) z))) ∧
    diagonalComplexification
        (G.continuumResolventTwoSidedConfluentBinomialNormalForm
          T hP hInnerSymmetric hSelf sigma rho m n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventTwoSidedConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho m n) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho hne m n z
  constructor
  · exact
      G.continuumResolventTwoSidedConfluentBinomialNormalFormDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf sigma rho hne m n
  · exact
      G.admissibleRescaledDefectResolventTwoSidedConfluentBinomialNormalFormDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf sigma rho hne m n

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
