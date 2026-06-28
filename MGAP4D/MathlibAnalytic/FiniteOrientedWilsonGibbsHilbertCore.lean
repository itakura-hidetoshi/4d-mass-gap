import Mathlib.Analysis.InnerProductSpace.PiL2
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonHeatBathWeightedFluctuationNorm

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Standard finite-dimensional Euclidean carrier for orientation-correct
Wilson observables after multiplication by the square root of the Gibbs
density. -/
abbrev FiniteOrientedLatticeWilsonSystem.GibbsHilbertSpace
    (L : FiniteOrientedLatticeWilsonSystem) : Type :=
  EuclideanSpace ℝ L.Configuration

noncomputable instance finiteOrientedLatticeWilsonConfigurationFintype
    (L : FiniteOrientedLatticeWilsonSystem) : Fintype L.Configuration := by
  classical
  exact Fintype.ofFinite L.Configuration

/-- Embed an oriented observable as the Euclidean vector `sqrt(mu) * f`. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsHilbertEmbedLinearMap
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

/-- The real oriented Gibbs probabilities sum to one. -/
theorem finite_oriented_gibbsProbabilityReal_sum_eq_one
    (L : FiniteOrientedLatticeWilsonSystem) :
    ∑ A : L.Configuration, L.gibbsProbabilityReal A = 1 := by
  simpa [FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal] using
    (finite_oriented_pmf_sum_toReal_eq_one L.gibbsPMF)

/-- Inner products of Gibbs-embedded oriented observables equal the native
Gibbs pairing. -/
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
      inner ℝ
          (Real.sqrt (L.gibbsProbabilityReal A) * f A)
          (Real.sqrt (L.gibbsProbabilityReal A) * g A) =
        L.gibbsProbabilityReal A * f A * g A
    change
      (Real.sqrt (L.gibbsProbabilityReal A) * g A) *
          (Real.sqrt (L.gibbsProbabilityReal A) * f A) =
        L.gibbsProbabilityReal A * f A * g A
    calc
      (Real.sqrt (L.gibbsProbabilityReal A) * g A) *
          (Real.sqrt (L.gibbsProbabilityReal A) * f A) =
        (Real.sqrt (L.gibbsProbabilityReal A)) ^ 2 * f A * g A := by
          ring
      _ = L.gibbsProbabilityReal A * f A * g A := by
        rw [Real.sq_sqrt
          (finite_oriented_gibbsProbabilityReal_nonneg L A)]

/-- Squared norm of the Gibbs embedding equals the native Gibbs pairing of an
observable with itself. -/
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
        (real_inner_self_eq_norm_sq
          (L.gibbsHilbertEmbedLinearMap f)).symm
    _ = L.gibbsPairingReal f f :=
      finite_oriented_gibbsHilbert_inner_embed L f f

end

end MathlibAnalytic
end MGAP4D
