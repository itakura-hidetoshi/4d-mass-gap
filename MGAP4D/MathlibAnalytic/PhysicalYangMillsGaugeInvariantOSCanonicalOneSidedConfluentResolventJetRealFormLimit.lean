import MGAP4D.MathlibAnalytic.ContinuousLinearMapOneSidedConfluentResolventJet
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventJetRealFormLimit

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

/-- The finite-time one-sided confluent jet normal form with arbitrary
multiplicity at `sigma` and one simple distinct node at `rho`. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventOneSidedConfluentJet
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.oneSidedConfluentResolventJetNormalForm
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau sigma.property)
    (G.admissibleRescaledDefectResolvent
      hInnerSymmetric tau rho.property)
    sigma.1 rho.1 n

/-- The corresponding continuum one-sided confluent resolvent jet. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventOneSidedConfluentJet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (n : ℕ) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.oneSidedConfluentResolventJetNormalForm
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf sigma.property)
    (G.vacuumOrthogonalContinuumRealResolvent
      T hP hInnerSymmetric hSelf rho.property)
    sigma.1 rho.1 n

/-- At finite time, the repeated-simple mixed product is exactly the one-sided
confluent jet normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_pow_mul_eq_oneSidedConfluentJet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ) :
    (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property) ^ n *
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau rho.property =
      G.admissibleRescaledDefectResolventOneSidedConfluentJet
        hInnerSymmetric tau sigma rho n := by
  apply
    ContinuousLinearMap.pow_mul_eq_oneSidedConfluentResolventJetNormalForm
  · exact hne
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau sigma.property rho.property

/-- In the continuum, the repeated-simple mixed product is exactly the same
one-sided confluent jet normal form. -/
theorem VacuumSemigroupGapSlope.continuumResolvent_pow_mul_eq_oneSidedConfluentJet
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property) ^ n *
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf rho.property =
      G.continuumResolventOneSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho n := by
  apply
    ContinuousLinearMap.pow_mul_eq_oneSidedConfluentResolventJetNormalForm
  · exact hne
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf sigma.property rho.property

/-- The finite-time confluent jet is exactly the existing singleton word-sum
whose word consists of `n` copies of `sigma` followed by `rho`. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventOneSidedConfluentJet_eq_finsetWordSum_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ) :
    G.admissibleRescaledDefectResolventOneSidedConfluentJet
        hInnerSymmetric tau sigma rho n =
      G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau ({()} : Finset Unit)
        (fun _ => List.replicate n sigma ++ [rho])
        (fun _ => 1) := by
  calc
    G.admissibleRescaledDefectResolventOneSidedConfluentJet
        hInnerSymmetric tau sigma rho n =
      (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property) ^ n *
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau rho.property :=
      (G.admissibleRescaledDefectResolvent_pow_mul_eq_oneSidedConfluentJet
        T hInnerSymmetric tau sigma rho hne n).symm
    _ = G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau ({()} : Finset Unit)
        (fun _ => List.replicate n sigma ++ [rho])
        (fun _ => 1) := by
      simp [VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetWordSum]

/-- The continuum confluent jet is the corresponding singleton continuum
resolvent word-sum. -/
theorem VacuumSemigroupGapSlope.continuumResolventOneSidedConfluentJet_eq_finsetWordSum_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ) :
    G.continuumResolventOneSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho n =
      G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf ({()} : Finset Unit)
        (fun _ => List.replicate n sigma ++ [rho])
        (fun _ => 1) := by
  calc
    G.continuumResolventOneSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho n =
      (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property) ^ n *
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf rho.property :=
      (G.continuumResolvent_pow_mul_eq_oneSidedConfluentJet
        T hP hInnerSymmetric hSelf sigma rho hne n).symm
    _ = G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf ({()} : Finset Unit)
        (fun _ => List.replicate n sigma ++ [rho])
        (fun _ => 1) := by
      simp [VacuumSemigroupGapSlope.continuumResolventFinsetWordSum]

/-- One-sided confluent jet normal forms converge pointwise strongly after
canonical diagonal complexification on the full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventOneSidedConfluentJetDiagonalComplexification_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ)
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventOneSidedConfluentJet
            hInnerSymmetric tau sigma rho n) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventOneSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho n) z)) := by
  have hSource :
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventOneSidedConfluentJet
            hInnerSymmetric tau sigma rho n) z) =
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventFinsetWordSum
            hInnerSymmetric tau ({()} : Finset Unit)
            (fun _ => List.replicate n sigma ++ [rho])
            (fun _ => 1)) z) := by
    funext tau
    rw [G.admissibleRescaledDefectResolventOneSidedConfluentJet_eq_finsetWordSum_singleton
      T hInnerSymmetric tau sigma rho hne n]
  have hTarget :
      diagonalComplexification
          (G.continuumResolventOneSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho n) z =
        diagonalComplexification
          (G.continuumResolventFinsetWordSum
            T hP hInnerSymmetric hSelf ({()} : Finset Unit)
            (fun _ => List.replicate n sigma ++ [rho])
            (fun _ => 1)) z := by
    rw [G.continuumResolventOneSidedConfluentJet_eq_finsetWordSum_singleton
      T hP hInnerSymmetric hSelf sigma rho hne n]
  rw [hSource, hTarget]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ => List.replicate n sigma ++ [rho]) (fun _ => 1) z

/-- The continuum one-sided confluent jet remains in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventOneSidedConfluentJetDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ) :
    diagonalComplexification
        (G.continuumResolventOneSidedConfluentJet
          T hP hInnerSymmetric hSelf sigma rho n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [G.continuumResolventOneSidedConfluentJet_eq_finsetWordSum_singleton
    T hP hInnerSymmetric hSelf sigma rho hne n]
  exact
    G.continuumResolventFinsetWordSumDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ => List.replicate n sigma ++ [rho]) (fun _ => 1)

/-- The bounded real operator underlying the complex strong limit of the
one-sided confluent jet exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventOneSidedConfluentJetDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventOneSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho n) := by
  rw [G.continuumResolventOneSidedConfluentJet_eq_finsetWordSum_singleton
    T hP hInnerSymmetric hSelf sigma rho hne n]
  exact
    G.admissibleRescaledDefectResolventFinsetWordSumDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf ({()} : Finset Unit)
      (fun _ => List.replicate n sigma ++ [rho]) (fun _ => 1)

/-- Any bounded real operator producing the same complex pointwise strong limit
is exactly the continuum one-sided confluent jet. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventOneSidedConfluentJet_real_limit_eq_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ)
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventOneSidedConfluentJet
              hInnerSymmetric tau sigma rho n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventOneSidedConfluentJet
      T hP hInnerSymmetric hSelf sigma rho n := by
  have hComplex :
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventOneSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho n) := by
    ext z
    exact tendsto_nhds_unique
      (hR z)
      (G.admissibleRescaledDefectResolventOneSidedConfluentJetDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho hne n z)
  apply
    (diagonalComplexificationLinearIsometry
      (H := P.VacuumOrthogonalHilbert)).injective
  simpa only [diagonalComplexificationLinearIsometry_apply] using hComplex

/-- Actual OS real-form strong-limit package for the one-sided confluent
resolvent jet normal form. -/
theorem VacuumSemigroupGapSlope.canonicalOneSidedConfluentResolventJetRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (sigma rho : G.BelowHalfMassShift)
    (hne : sigma.1 ≠ rho.1)
    (n : ℕ) :
    (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventOneSidedConfluentJet
              hInnerSymmetric tau sigma rho n) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝
          (diagonalComplexification
            (G.continuumResolventOneSidedConfluentJet
              T hP hInnerSymmetric hSelf sigma rho n) z))) ∧
    diagonalComplexification
        (G.continuumResolventOneSidedConfluentJet
          T hP hInnerSymmetric hSelf sigma rho n) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) ∧
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventOneSidedConfluentJet
            T hP hInnerSymmetric hSelf sigma rho n) := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventOneSidedConfluentJetDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf sigma rho hne n z
  constructor
  · exact
      G.continuumResolventOneSidedConfluentJetDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf sigma rho hne n
  · exact
      G.admissibleRescaledDefectResolventOneSidedConfluentJetDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf sigma rho hne n

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
