import MGAP4D.MathlibAnalytic.ContinuousLinearMapTwoSidedConfluentResolventJet
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalOneSidedConfluentResolventJetRealFormLimit

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

/-- The finite-time two-sided confluent jet normal form with arbitrary finite
multiplicity at each of two below-half-mass nodes. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentJet
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (m n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.twoSidedConfluentResolventJetNormalForm
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau sigma.property)
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau rho.property)
    sigma.1 rho.1 m n

/-- The corresponding continuum two-sided confluent resolvent jet. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventTwoSidedConfluentJet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (m n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.twoSidedConfluentResolventJetNormalForm
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf sigma.property)
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf rho.property)
    sigma.1 rho.1 m n

/-- At finite time, the arbitrary two-block mixed product is exactly the
corresponding two-sided confluent jet normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_pow_mul_pow_eq_twoSidedConfluentJet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property) ^ m *
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau rho.property) ^ n =
      G.admissibleRescaledDefectResolventTwoSidedConfluentJet
        hInnerSymmetric tau sigma rho m n := by
  apply
    ContinuousLinearMap.pow_mul_pow_eq_twoSidedConfluentResolventJetNormalForm
  · exact hne
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau sigma.property rho.property

/-- In the continuum, the arbitrary two-block mixed product is exactly the same
two-sided confluent jet normal form. -/
theorem VacuumSemigroupGapSlope.continuumResolvent_pow_mul_pow_eq_twoSidedConfluentJet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property) ^ m *
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf rho.property) ^ n =
      G.continuumResolventTwoSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho m n := by
  apply
    ContinuousLinearMap.pow_mul_pow_eq_twoSidedConfluentResolventJetNormalForm
  · exact hne
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf sigma.property rho.property

/-- The finite-time two-sided confluent jet is exactly the existing singleton
word-sum with two repeated blocks. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentJet_eq_finsetWordSum_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    G.admissibleRescaledDefectResolventTwoSidedConfluentJet
        hInnerSymmetric tau sigma rho m n =
      G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau ({()} : Finset Unit)
        (fun _ => List.replicate m sigma ++ List.replicate n rho)
        (fun _ => 1) := by
  calc
    G.admissibleRescaledDefectResolventTwoSidedConfluentJet
        hInnerSymmetric tau sigma rho m n =
      (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property) ^ m *
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau rho.property) ^ n :=
      (G.admissibleRescaledDefectResolvent_pow_mul_pow_eq_twoSidedConfluentJet
        T hInnerSymmetric tau sigma rho hne m n).symm
    _ = G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau ({()} : Finset Unit)
        (fun _ => List.replicate m sigma ++ List.replicate n rho)
        (fun _ => 1) := by
      simp [VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum]

/-- The continuum two-sided confluent jet is the corresponding singleton
continuum resolvent word-sum. -/
theorem VacuumSemigroupGapSlope.continuumResolventTwoSidedConfluentJet_eq_finsetWordSum_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    G.continuumResolventTwoSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho m n =
      G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf ({()} : Finset Unit)
        (fun _ => List.replicate m sigma ++ List.replicate n rho)
        (fun _ => 1) := by
  calc
    G.continuumResolventTwoSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho m n =
      (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property) ^ m *
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf rho.property) ^ n :=
      (G.continuumResolvent_pow_mul_pow_eq_twoSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho hne m n).symm
    _ = G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf ({()} : Finset Unit)
        (fun _ => List.replicate m sigma ++ List.replicate n rho)
        (fun _ => 1) := by
      simp [VacuumSemigroupGapSlope.continuumResolventFinsetWordSum]

/-- Two-sided confluent jet normal forms converge pointwise strongly after
canonical diagonal complexification on the full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentJetDiagonalComplexification_tendsto_continuum
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
          (G.admissibleRescaledDefectResolventTwoSidedConfluentJet
            hInnerSymmetric tau sigma rho m n) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventTwoSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho m n) z)) := by
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventTwoSidedConfluentJet
            hInnerSymmetric tau sigma rho m n) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau ({()} : Finset Unit)
            (fun _ => List.replicate m sigma ++ List.replicate n rho)
            (fun _ => 1)) z) := by
    funext tau
    rw [G.admissibleRescaledDefectResolventTwoSidedConfluentJet_eq_finsetWordSum_singleton
      T hInnerSymmetric tau sigma rho hne m n]
  have hTarget :
      diagonalComplexification
          (G.continuumResolventTwoSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho m n) z =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf ({()} : Finset Unit)
            (fun _ => List.replicate m sigma ++ List.replicate n rho)
            (fun _ => 1)) z := by
    rw [G.continuumResolventTwoSidedConfluentJet_eq_finsetWordSum_singleton
      T hP hInnerSymmetric hSelf sigma rho hne m n]
  rw [hSource, hTarget]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ => List.replicate m sigma ++ List.replicate n rho)
      (fun _ => 1) z

/-- The continuum two-sided confluent jet remains in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventTwoSidedConfluentJetDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (m n : ℕ) :
    diagonalComplexification
        (G.continuumResolventTwoSidedConfluentJet
          T hP hInnerSymmetric hSelf sigma rho m n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [G.continuumResolventTwoSidedConfluentJet_eq_finsetWordSum_singleton
    T hP hInnerSymmetric hSelf sigma rho hne m n]
  exact
    G.continuumResolventFinsetWordSumDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ => List.replicate m sigma ++ List.replicate n rho)
      (fun _ => 1)

/-- The bounded real operator underlying the complex strong limit of the
two-sided confluent jet exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentJetDiagonalComplexification_existsUnique_real_limit
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
          (G.continuumResolventTwoSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho m n) := by
  rw [G.continuumResolventTwoSidedConfluentJet_eq_finsetWordSum_singleton
    T hP hInnerSymmetric hSelf sigma rho hne m n]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ => List.replicate m sigma ++ List.replicate n rho)
      (fun _ => 1)

/-- Any bounded real operator producing the same complex pointwise strong limit
is exactly the continuum two-sided confluent jet. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventTwoSidedConfluentJet_real_limit_eq_continuum
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
            (G.admissibleRescaledDefectResolventTwoSidedConfluentJet
              hInnerSymmetric tau sigma rho m n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventTwoSidedConfluentJet
      T hP hInnerSymmetric hSelf sigma rho m n := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventTwoSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho m n) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectResolventTwoSidedConfluentJetDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho hne m n z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual OS real-form strong-limit package for arbitrary finite multiplicities
at two distinct resolvent nodes. -/
theorem VacuumSemigroupGapSlope.canonicalTwoSidedConfluentResolventJetRealFormStrongLimitPackage
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
            (G.admissibleRescaledDefectResolventTwoSidedConfluentJet
              hInnerSymmetric tau sigma rho m n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventTwoSidedConfluentJet
              T hP hInnerSymmetric hSelf sigma rho m n) z))) ∧
    diagonalComplexification
        (G.continuumResolventTwoSidedConfluentJet
          T hP hInnerSymmetric hSelf sigma rho m n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventTwoSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho m n) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventTwoSidedConfluentJetDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho hne m n z
  constructor
  · exact
      G.continuumResolventTwoSidedConfluentJetDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf sigma rho hne m n
  · exact
      G.admissibleRescaledDefectResolventTwoSidedConfluentJetDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf sigma rho hne m n

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
