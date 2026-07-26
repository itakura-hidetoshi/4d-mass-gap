import MGAP4D.MathlibAnalytic.ContinuousLinearMapThreeNodeConfluentResolventBinomialNormalForm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalTwoSidedConfluentResolventBinomialRealFormLimit

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

/-- The finite-time iterated closed binomial normal form for positive
multiplicities at three pairwise-distinct below-half-mass resolvent nodes. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho theta : G.BelowHalfMassShift)
    (m n p : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.threeNodeConfluentResolventBinomialNormalForm
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau sigma.property)
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau rho.property)
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau theta.property)
    sigma.1 rho.1 theta.1 m n p

/-- The corresponding continuum three-node iterated binomial normal form. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventThreeNodeConfluentBinomialNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (m n p : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.threeNodeConfluentResolventBinomialNormalForm
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf sigma.property)
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf rho.property)
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf theta.property)
    sigma.1 rho.1 theta.1 m n p

/-- At finite time, the positive three-block mixed product is exactly the
three-node iterated closed binomial normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_three_pow_succ_product_eq_binomialNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ) :
    ((G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property) ^ (m + 1) *
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau rho.property) ^ (n + 1)) *
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau theta.property) ^ (p + 1) =
      G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
        hInnerSymmetric tau sigma rho theta m n p := by
  apply
    ContinuousLinearMap.pow_succ_mul_pow_succ_mul_pow_succ_eq_threeNodeConfluentResolventBinomialNormalForm
  · exact hneSigmaRho
  · exact hneSigmaTheta
  · exact hneRhoTheta
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau sigma.property rho.property
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau sigma.property theta.property
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau rho.property theta.property

/-- In the continuum, the positive three-block mixed product has the same
three-node iterated binomial normal form. -/
theorem VacuumSemigroupGapSlope.continuumResolvent_three_pow_succ_product_eq_binomialNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ) :
    ((G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property) ^ (m + 1) *
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf rho.property) ^ (n + 1)) *
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf theta.property) ^ (p + 1) =
      G.continuumResolventThreeNodeConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf sigma rho theta m n p := by
  apply
    ContinuousLinearMap.pow_succ_mul_pow_succ_mul_pow_succ_eq_threeNodeConfluentResolventBinomialNormalForm
  · exact hneSigmaRho
  · exact hneSigmaTheta
  · exact hneRhoTheta
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf sigma.property rho.property
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf sigma.property theta.property
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf rho.property theta.property

/-- The finite-time three-node normal form is exactly the existing singleton
word-sum with three repeated positive blocks. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm_eq_finsetWordSum_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ) :
    G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
        hInnerSymmetric tau sigma rho theta m n p =
      G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau ({()} : Finset Unit)
        (fun _ =>
          List.replicate (m + 1) sigma ++
            List.replicate (n + 1) rho ++
              List.replicate (p + 1) theta)
        (fun _ => 1) := by
  calc
    G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
        hInnerSymmetric tau sigma rho theta m n p =
      ((G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property) ^ (m + 1) *
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau rho.property) ^ (n + 1)) *
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau theta.property) ^ (p + 1) :=
      (G.admissibleRescaledDefectResolvent_three_pow_succ_product_eq_binomialNormalForm
        T hInnerSymmetric tau sigma rho theta
        hneSigmaRho hneSigmaTheta hneRhoTheta m n p).symm
    _ = G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau ({()} : Finset Unit)
        (fun _ =>
          List.replicate (m + 1) sigma ++
            List.replicate (n + 1) rho ++
              List.replicate (p + 1) theta)
        (fun _ => 1) := by
      simp [VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum]

/-- The continuum three-node normal form is the corresponding singleton
continuum resolvent word-sum. -/
theorem VacuumSemigroupGapSlope.continuumResolventThreeNodeConfluentBinomialNormalForm_eq_finsetWordSum_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ) :
    G.continuumResolventThreeNodeConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf sigma rho theta m n p =
      G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf ({()} : Finset Unit)
        (fun _ =>
          List.replicate (m + 1) sigma ++
            List.replicate (n + 1) rho ++
              List.replicate (p + 1) theta)
        (fun _ => 1) := by
  calc
    G.continuumResolventThreeNodeConfluentBinomialNormalForm
        T hP hInnerSymmetric hSelf sigma rho theta m n p =
      ((G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property) ^ (m + 1) *
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf rho.property) ^ (n + 1)) *
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf theta.property) ^ (p + 1) :=
      (G.continuumResolvent_three_pow_succ_product_eq_binomialNormalForm
        T hP hInnerSymmetric hSelf sigma rho theta
        hneSigmaRho hneSigmaTheta hneRhoTheta m n p).symm
    _ = G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf ({()} : Finset Unit)
        (fun _ =>
          List.replicate (m + 1) sigma ++
            List.replicate (n + 1) rho ++
              List.replicate (p + 1) theta)
        (fun _ => 1) := by
      simp [VacuumSemigroupGapSlope.continuumResolventFinsetWordSum]

/-- Three-node iterated binomial normal forms converge pointwise strongly after
canonical diagonal complexification on the full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
            hInnerSymmetric tau sigma rho theta m n p) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventThreeNodeConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho theta m n p) z)) := by
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
            hInnerSymmetric tau sigma rho theta m n p) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau ({()} : Finset Unit)
            (fun _ =>
              List.replicate (m + 1) sigma ++
                List.replicate (n + 1) rho ++
                  List.replicate (p + 1) theta)
            (fun _ => 1)) z) := by
    funext tau
    rw [G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm_eq_finsetWordSum_singleton
      T hInnerSymmetric tau sigma rho theta
      hneSigmaRho hneSigmaTheta hneRhoTheta m n p]
  have hTarget :
      diagonalComplexification
          (G.continuumResolventThreeNodeConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho theta m n p) z =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf ({()} : Finset Unit)
            (fun _ =>
              List.replicate (m + 1) sigma ++
                List.replicate (n + 1) rho ++
                  List.replicate (p + 1) theta)
            (fun _ => 1)) z := by
    rw [G.continuumResolventThreeNodeConfluentBinomialNormalForm_eq_finsetWordSum_singleton
      T hP hInnerSymmetric hSelf sigma rho theta
      hneSigmaRho hneSigmaTheta hneRhoTheta m n p]
  rw [hSource, hTarget]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ =>
        List.replicate (m + 1) sigma ++
          List.replicate (n + 1) rho ++
            List.replicate (p + 1) theta)
      (fun _ => 1) z

/-- The continuum three-node normal form remains in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventThreeNodeConfluentBinomialNormalFormDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ) :
    diagonalComplexification
        (G.continuumResolventThreeNodeConfluentBinomialNormalForm
          T hP hInnerSymmetric hSelf sigma rho theta m n p) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [G.continuumResolventThreeNodeConfluentBinomialNormalForm_eq_finsetWordSum_singleton
    T hP hInnerSymmetric hSelf sigma rho theta
    hneSigmaRho hneSigmaTheta hneRhoTheta m n p]
  exact
    G.continuumResolventFinsetWordSumDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ =>
        List.replicate (m + 1) sigma ++
          List.replicate (n + 1) rho ++
            List.replicate (p + 1) theta)
      (fun _ => 1)

/-- The bounded real operator underlying the complex strong limit of the
three-node normal form exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalFormDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventThreeNodeConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho theta m n p) := by
  rw [G.continuumResolventThreeNodeConfluentBinomialNormalForm_eq_finsetWordSum_singleton
    T hP hInnerSymmetric hSelf sigma rho theta
    hneSigmaRho hneSigmaTheta hneRhoTheta m n p]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ =>
        List.replicate (m + 1) sigma ++
          List.replicate (n + 1) rho ++
            List.replicate (p + 1) theta)
      (fun _ => 1)

/-- Any bounded real operator producing the same complex pointwise strong limit
is exactly the continuum three-node normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm_real_limit_eq_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
              hInnerSymmetric tau sigma rho theta m n p) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventThreeNodeConfluentBinomialNormalForm
      T hP hInnerSymmetric hSelf sigma rho theta m n p := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventThreeNodeConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho theta m n p) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho theta
        hneSigmaRho hneSigmaTheta hneRhoTheta m n p z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual OS real-form strong-limit package for the iterated three-node closed
confluent binomial normal form. -/
theorem VacuumSemigroupGapSlope.canonicalThreeNodeConfluentResolventBinomialRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho theta : G.BelowHalfMassShift)
    (hneSigmaRho : sigma.1 ≠ rho.1)
    (hneSigmaTheta : sigma.1 ≠ theta.1)
    (hneRhoTheta : rho.1 ≠ theta.1)
    (m n p : ℕ) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalForm
              hInnerSymmetric tau sigma rho theta m n p) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventThreeNodeConfluentBinomialNormalForm
              T hP hInnerSymmetric hSelf sigma rho theta m n p) z))) ∧
    diagonalComplexification
        (G.continuumResolventThreeNodeConfluentBinomialNormalForm
          T hP hInnerSymmetric hSelf sigma rho theta m n p) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventThreeNodeConfluentBinomialNormalForm
            T hP hInnerSymmetric hSelf sigma rho theta m n p) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho theta
        hneSigmaRho hneSigmaTheta hneRhoTheta m n p z
  constructor
  · exact
      G.continuumResolventThreeNodeConfluentBinomialNormalFormDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf sigma rho theta
        hneSigmaRho hneSigmaTheta hneRhoTheta m n p
  · exact
      G.admissibleRescaledDefectResolventThreeNodeConfluentBinomialNormalFormDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf sigma rho theta
        hneSigmaRho hneSigmaTheta hneRhoTheta m n p

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
