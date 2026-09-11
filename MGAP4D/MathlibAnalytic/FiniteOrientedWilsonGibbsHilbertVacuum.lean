import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsHilbertCore
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumPoincareHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Native oriented Gibbs Hilbert vacuum: the embedded constant-one
observable. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsHilbertVacuum
    (L : FiniteOrientedLatticeWilsonSystem) : L.GibbsHilbertSpace :=
  L.gibbsHilbertEmbedLinearMap
    (fun _ : L.Configuration => (1 : ℝ))

/-- The native oriented Gibbs Hilbert vacuum is normalized. -/
theorem finite_oriented_gibbsHilbertVacuum_norm
    (L : FiniteOrientedLatticeWilsonSystem) :
    ‖L.gibbsHilbertVacuum‖ = 1 := by
  have hsq : ‖L.gibbsHilbertVacuum‖ ^ 2 = (1 : ℝ) := by
    rw [FiniteOrientedLatticeWilsonSystem.gibbsHilbertVacuum,
      EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ A : L.Configuration,
          (L.gibbsHilbertEmbedLinearMap
            (fun _ : L.Configuration => (1 : ℝ)) A) ^ 2 =
        ∑ A : L.Configuration, L.gibbsProbabilityReal A := by
          apply Finset.sum_congr rfl
          intro A _hA
          rw [finite_oriented_gibbsHilbertEmbedLinearMap_apply]
          simp only
          rw [mul_one,
            Real.sq_sqrt
              (finite_oriented_gibbsProbabilityReal_nonneg L A)]
      _ = 1 := finite_oriented_gibbsProbabilityReal_sum_eq_one L
  nlinarith [norm_nonneg L.gibbsHilbertVacuum]

/-- Vacuum expectation of a Gibbs-embedded oriented observable is its Gibbs
expectation. -/
theorem finite_oriented_gibbsHilbert_inner_vacuum_embed
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    inner ℝ L.gibbsHilbertVacuum
        (L.gibbsHilbertEmbedLinearMap f) =
      L.gibbsExpectationReal f := by
  rw [FiniteOrientedLatticeWilsonSystem.gibbsHilbertVacuum,
    finite_oriented_gibbsHilbert_inner_embed]
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Center an oriented Wilson observable by subtracting its Gibbs expectation. -/
def FiniteOrientedLatticeWilsonSystem.gibbsCenteredObservable
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : L.Configuration → ℝ :=
  fun A => f A - L.gibbsExpectationReal f

/-- Vacuum centering in the native Gibbs Hilbert realization equals Gibbs
centering of the underlying observable. -/
theorem finite_oriented_gibbsHilbert_vacuumCentered_embed
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    finiteVacuumCentered L.gibbsHilbertVacuum
        (L.gibbsHilbertEmbedLinearMap f) =
      L.gibbsHilbertEmbedLinearMap (L.gibbsCenteredObservable f) := by
  unfold finiteVacuumCentered
  rw [finite_oriented_gibbsHilbert_inner_vacuum_embed]
  change
    L.gibbsHilbertEmbedLinearMap f -
        L.gibbsExpectationReal f •
          L.gibbsHilbertEmbedLinearMap
            (fun _ : L.Configuration => (1 : ℝ)) =
      L.gibbsHilbertEmbedLinearMap (L.gibbsCenteredObservable f)
  calc
    L.gibbsHilbertEmbedLinearMap f -
        L.gibbsExpectationReal f •
          L.gibbsHilbertEmbedLinearMap
            (fun _ : L.Configuration => (1 : ℝ)) =
      L.gibbsHilbertEmbedLinearMap
        (f - L.gibbsExpectationReal f •
          (fun _ : L.Configuration => (1 : ℝ))) := by
            symm
            rw [map_sub, map_smul]
    _ = L.gibbsHilbertEmbedLinearMap (L.gibbsCenteredObservable f) := by
      apply congrArg L.gibbsHilbertEmbedLinearMap
      funext A
      simp [FiniteOrientedLatticeWilsonSystem.gibbsCenteredObservable]

/-- The squared norm of the vacuum-centered native Gibbs Hilbert vector equals
oriented Gibbs variance. -/
theorem finite_oriented_gibbsHilbert_vacuumCentered_norm_sq
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    ‖finiteVacuumCentered L.gibbsHilbertVacuum
        (L.gibbsHilbertEmbedLinearMap f)‖ ^ 2 =
      L.gibbsVarianceReal f := by
  rw [finite_oriented_gibbsHilbert_vacuumCentered_embed,
    finite_oriented_gibbsHilbert_norm_sq_embed]
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.gibbsCenteredObservable
    FiniteOrientedLatticeWilsonSystem.gibbsVarianceReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

end

end MathlibAnalytic
end MGAP4D
