import Mathlib.Analysis.InnerProductSpace.PiL2
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathPairingSymmetry
import MGAP4D.MathlibAnalytic.FiniteWilsonVacuumPoincareHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

abbrev FiniteOrientedLatticeWilsonSystem.GibbsHilbertSpace
    (L : FiniteOrientedLatticeWilsonSystem) : Type :=
  EuclideanSpace ℝ L.Configuration

noncomputable def FiniteOrientedLatticeWilsonSystem.gibbsHilbertEmbedLinearMap
    (L : FiniteOrientedLatticeWilsonSystem) :
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

@[simp] theorem finite_oriented_gibbsHilbertEmbedLinearMap_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration) :
    L.gibbsHilbertEmbedLinearMap f A =
      Real.sqrt (L.gibbsProbabilityReal A) * f A :=
  rfl

theorem finite_oriented_gibbsProbabilityReal_sum_eq_one
    (L : FiniteOrientedLatticeWilsonSystem) :
    ∑ A : L.Configuration, L.gibbsProbabilityReal A = 1 := by
  simpa [FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal] using
    (finite_pmf_sum_toReal_eq_one L.gibbsPMF)

theorem finite_oriented_gibbsHilbert_inner_embed
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    inner ℝ (L.gibbsHilbertEmbedLinearMap f)
        (L.gibbsHilbertEmbedLinearMap g) =
      L.gibbsPairingReal f g := by
  classical
  rw [PiLp.inner_apply]
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  apply Finset.sum_congr
  · ext A
    simp
  · intro A _hA
    change
      (Real.sqrt (L.gibbsProbabilityReal A) * g A) *
          (Real.sqrt (L.gibbsProbabilityReal A) * f A) =
        L.gibbsProbabilityReal A * f A * g A
    calc
      (Real.sqrt (L.gibbsProbabilityReal A) * g A) *
          (Real.sqrt (L.gibbsProbabilityReal A) * f A) =
        (Real.sqrt (L.gibbsProbabilityReal A)) ^ 2 * f A * g A := by ring
      _ = L.gibbsProbabilityReal A * f A * g A := by
        rw [Real.sq_sqrt (finite_oriented_gibbsProbabilityReal_nonneg L A)]

theorem finite_oriented_gibbsHilbert_norm_sq_embed
    (L : FiniteOrientedLatticeWilsonSystem)
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
      finite_oriented_gibbsHilbert_inner_embed L f f

noncomputable def FiniteOrientedLatticeWilsonSystem.gibbsHilbertVacuum
    (L : FiniteOrientedLatticeWilsonSystem) : L.GibbsHilbertSpace :=
  L.gibbsHilbertEmbedLinearMap (fun _ : L.Configuration => (1 : ℝ))

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
          Real.sq_sqrt (finite_oriented_gibbsProbabilityReal_nonneg L A)]
      _ = 1 := finite_oriented_gibbsProbabilityReal_sum_eq_one L
  nlinarith [norm_nonneg L.gibbsHilbertVacuum]

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

def FiniteOrientedLatticeWilsonSystem.gibbsCenteredObservable
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : L.Configuration → ℝ :=
  fun A => f A - L.gibbsExpectationReal f

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
