import Mathlib.Analysis.InnerProductSpace.PiL2
import MGAP4D.MathlibAnalytic.FiniteWilsonHeatBathWeightedFluctuationNorm
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumPoincareHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Standard finite-dimensional Euclidean carrier for Wilson observables after
multiplication by the square root of the Gibbs density. -/
abbrev FiniteLatticeWilsonSystem.GibbsHilbertSpace
    (L : FiniteLatticeWilsonSystem) : Type :=
  EuclideanSpace ℝ L.Configuration

/-- Embed a real observable as the Euclidean vector `sqrt(mu) * f`. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsHilbertEmbedLinearMap
    (L : FiniteLatticeWilsonSystem) :
    (L.Configuration → ℝ) →ₗ[ℝ] L.GibbsHilbertSpace where
  toFun f :=
    WithLp.toLp 2 fun A : L.Configuration =>
      Real.sqrt (L.gibbsProbabilityReal A) * f A
  map_add' f g := by
    ext A
    change Real.sqrt (L.gibbsProbabilityReal A) * (f A + g A) =
      Real.sqrt (L.gibbsProbabilityReal A) * f A +
        Real.sqrt (L.gibbsProbabilityReal A) * g A
    ring
  map_smul' c f := by
    ext A
    change Real.sqrt (L.gibbsProbabilityReal A) * (c * f A) =
      c * (Real.sqrt (L.gibbsProbabilityReal A) * f A)
    ring

@[simp] theorem finite_lattice_gibbsHilbertEmbedLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) (A : L.Configuration) :
    L.gibbsHilbertEmbedLinearMap f A =
      Real.sqrt (L.gibbsProbabilityReal A) * f A :=
  rfl

/-- The real Gibbs probabilities sum to one. -/
theorem finite_lattice_gibbsProbabilityReal_sum_eq_one
    (L : FiniteLatticeWilsonSystem) :
    ∑ A : L.Configuration, L.gibbsProbabilityReal A = 1 := by
  simpa [FiniteLatticeWilsonSystem.gibbsProbabilityReal] using
    (finite_pmf_sum_toReal_eq_one L.gibbsPMF)

/-- The Euclidean inner product of Gibbs-embedded observables is exactly the
finite Wilson Gibbs pairing. -/
theorem finite_lattice_gibbsHilbert_inner_embed
    (L : FiniteLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    inner ℝ (L.gibbsHilbertEmbedLinearMap f)
        (L.gibbsHilbertEmbedLinearMap g) =
      L.gibbsPairingReal f g := by
  classical
  rw [PiLp.inner_apply]
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
  apply Finset.sum_congr
  · ext A
    simp
  · intro A _hA
    change
      (Real.sqrt (L.gibbsProbabilityReal A) * f A) *
          (Real.sqrt (L.gibbsProbabilityReal A) * g A) =
        L.gibbsProbabilityReal A * f A * g A
    calc
      (Real.sqrt (L.gibbsProbabilityReal A) * f A) *
          (Real.sqrt (L.gibbsProbabilityReal A) * g A) =
        (Real.sqrt (L.gibbsProbabilityReal A)) ^ 2 * f A * g A := by
          ring
      _ = L.gibbsProbabilityReal A * f A * g A := by
        rw [Real.sq_sqrt (finite_lattice_gibbsProbabilityReal_nonneg L A)]

/-- The squared Euclidean norm of the Gibbs embedding is the Gibbs pairing of
an observable with itself. -/
theorem finite_lattice_gibbsHilbert_norm_sq_embed
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    ‖L.gibbsHilbertEmbedLinearMap f‖ ^ 2 =
      L.gibbsPairingReal f f := by
  calc
    ‖L.gibbsHilbertEmbedLinearMap f‖ ^ 2 =
        inner ℝ (L.gibbsHilbertEmbedLinearMap f)
          (L.gibbsHilbertEmbedLinearMap f) := by
      simpa using
        (real_inner_self_eq_norm_sq (L.gibbsHilbertEmbedLinearMap f)).symm
    _ = L.gibbsPairingReal f f :=
      finite_lattice_gibbsHilbert_inner_embed L f f

/-- The finite Wilson vacuum vector is the Gibbs embedding of the constant-one
observable. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsHilbertVacuum
    (L : FiniteLatticeWilsonSystem) : L.GibbsHilbertSpace :=
  L.gibbsHilbertEmbedLinearMap (fun _ : L.Configuration => (1 : ℝ))

/-- The Gibbs Hilbert vacuum is normalized. -/
theorem finite_lattice_gibbsHilbertVacuum_norm
    (L : FiniteLatticeWilsonSystem) :
    ‖L.gibbsHilbertVacuum‖ = 1 := by
  have hsq : ‖L.gibbsHilbertVacuum‖ ^ 2 = (1 : ℝ) := by
    rw [FiniteLatticeWilsonSystem.gibbsHilbertVacuum,
      EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ A : L.Configuration,
          (L.gibbsHilbertEmbedLinearMap
            (fun _ : L.Configuration => (1 : ℝ)) A) ^ 2 =
          ∑ A : L.Configuration, L.gibbsProbabilityReal A := by
        apply Finset.sum_congr rfl
        intro A _hA
        rw [finite_lattice_gibbsHilbertEmbedLinearMap_apply]
        simp only
        rw [mul_one,
          Real.sq_sqrt (finite_lattice_gibbsProbabilityReal_nonneg L A)]
      _ = 1 := finite_lattice_gibbsProbabilityReal_sum_eq_one L
  nlinarith [norm_nonneg L.gibbsHilbertVacuum]

/-- Vacuum expectation of a Gibbs-embedded observable is its finite Wilson
Gibbs expectation. -/
theorem finite_lattice_gibbsHilbert_inner_vacuum_embed
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    inner ℝ L.gibbsHilbertVacuum
        (L.gibbsHilbertEmbedLinearMap f) =
      L.gibbsExpectationReal f := by
  rw [FiniteLatticeWilsonSystem.gibbsHilbertVacuum,
    finite_lattice_gibbsHilbert_inner_embed]
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
    FiniteLatticeWilsonSystem.gibbsExpectationReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Center a Wilson observable by subtracting its Gibbs expectation. -/
def FiniteLatticeWilsonSystem.gibbsCenteredObservable
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : L.Configuration → ℝ :=
  fun A => f A - L.gibbsExpectationReal f

/-- Vacuum centering in the Euclidean Gibbs realization is exactly Gibbs
centering of the underlying observable. -/
theorem finite_lattice_gibbsHilbert_vacuumCentered_embed
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    finiteVacuumCentered L.gibbsHilbertVacuum
        (L.gibbsHilbertEmbedLinearMap f) =
      L.gibbsHilbertEmbedLinearMap (L.gibbsCenteredObservable f) := by
  unfold finiteVacuumCentered
  rw [finite_lattice_gibbsHilbert_inner_vacuum_embed]
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
      simp [FiniteLatticeWilsonSystem.gibbsCenteredObservable]

/-- The squared norm of the vacuum-centered Gibbs Hilbert vector is exactly the
finite Wilson Gibbs variance. -/
theorem finite_lattice_gibbsHilbert_vacuumCentered_norm_sq
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    ‖finiteVacuumCentered L.gibbsHilbertVacuum
        (L.gibbsHilbertEmbedLinearMap f)‖ ^ 2 =
      L.gibbsVarianceReal f := by
  rw [finite_lattice_gibbsHilbert_vacuumCentered_embed,
    finite_lattice_gibbsHilbert_norm_sq_embed]
  unfold FiniteLatticeWilsonSystem.gibbsPairingReal
    FiniteLatticeWilsonSystem.gibbsCenteredObservable
    FiniteLatticeWilsonSystem.gibbsVarianceReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

end

end MathlibAnalytic
end MGAP4D
