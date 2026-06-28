import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonGibbsHilbertVacuum

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every oriented finite-volume Gibbs configuration has strictly positive real
probability. -/
theorem finite_oriented_gibbsProbabilityReal_pos
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    0 < L.gibbsProbabilityReal A := by
  unfold FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  apply ENNReal.toReal_pos
  · rw [finite_oriented_gibbsPMF_apply]
    exact mul_ne_zero
      (finite_oriented_boltzmannWeight_ne_zero L A)
      (ENNReal.inv_ne_zero.mpr
        (finite_oriented_partitionFunction_ne_top L))
  · exact L.gibbsPMF.apply_ne_top A

/-- The square root of every oriented Gibbs probability is nonzero. -/
theorem finite_oriented_sqrt_gibbsProbabilityReal_ne_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration) :
    Real.sqrt (L.gibbsProbabilityReal A) ≠ 0 :=
  ne_of_gt
    (Real.sqrt_pos.2 (finite_oriented_gibbsProbabilityReal_pos L A))

/-- Recover an observable from a native Gibbs Hilbert vector by pointwise
division by `sqrt(mu)`. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsHilbertObserveLinearMap
    (L : FiniteOrientedLatticeWilsonSystem) :
    L.GibbsHilbertSpace →ₗ[ℝ] (L.Configuration → ℝ) where
  toFun x := fun A => x A / Real.sqrt (L.gibbsProbabilityReal A)
  map_add' x y := by
    funext A
    change
      (x A + y A) / Real.sqrt (L.gibbsProbabilityReal A) =
        x A / Real.sqrt (L.gibbsProbabilityReal A) +
          y A / Real.sqrt (L.gibbsProbabilityReal A)
    ring
  map_smul' c x := by
    funext A
    change
      (c * x A) / Real.sqrt (L.gibbsProbabilityReal A) =
        c * (x A / Real.sqrt (L.gibbsProbabilityReal A))
    ring

@[simp] theorem finite_oriented_gibbsHilbertObserveLinearMap_apply
    (L : FiniteOrientedLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace)
    (A : L.Configuration) :
    L.gibbsHilbertObserveLinearMap x A =
      x A / Real.sqrt (L.gibbsProbabilityReal A) :=
  rfl

/-- Observing an embedded oriented observable recovers the observable. -/
theorem finite_oriented_gibbsHilbert_observe_embed
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsHilbertObserveLinearMap
        (L.gibbsHilbertEmbedLinearMap f) = f := by
  funext A
  rw [finite_oriented_gibbsHilbertObserveLinearMap_apply,
    finite_oriented_gibbsHilbertEmbedLinearMap_apply]
  field_simp [finite_oriented_sqrt_gibbsProbabilityReal_ne_zero L A]

/-- Embedding the observable recovered from a native Gibbs Hilbert vector
returns the vector. -/
theorem finite_oriented_gibbsHilbert_embed_observe
    (L : FiniteOrientedLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    L.gibbsHilbertEmbedLinearMap
        (L.gibbsHilbertObserveLinearMap x) = x := by
  ext A
  rw [finite_oriented_gibbsHilbertEmbedLinearMap_apply,
    finite_oriented_gibbsHilbertObserveLinearMap_apply]
  field_simp [finite_oriented_sqrt_gibbsProbabilityReal_ne_zero L A]

/-- Multiplication by `sqrt(mu)` is a linear equivalence from oriented
observables to the concrete native Gibbs Hilbert space. -/
noncomputable def
    FiniteOrientedLatticeWilsonSystem.gibbsHilbertLinearEquiv
    (L : FiniteOrientedLatticeWilsonSystem) :
    (L.Configuration → ℝ) ≃ₗ[ℝ] L.GibbsHilbertSpace :=
  LinearEquiv.ofBijective L.gibbsHilbertEmbedLinearMap
    ⟨by
      intro f g hfg
      calc
        f = L.gibbsHilbertObserveLinearMap
            (L.gibbsHilbertEmbedLinearMap f) :=
          (finite_oriented_gibbsHilbert_observe_embed L f).symm
        _ = L.gibbsHilbertObserveLinearMap
            (L.gibbsHilbertEmbedLinearMap g) := by
          exact congrArg
            (fun x : L.GibbsHilbertSpace =>
              L.gibbsHilbertObserveLinearMap x) hfg
        _ = g := finite_oriented_gibbsHilbert_observe_embed L g,
    by
      intro x
      exact ⟨L.gibbsHilbertObserveLinearMap x,
        finite_oriented_gibbsHilbert_embed_observe L x⟩⟩

/-- Vacuum centering of an arbitrary native Gibbs Hilbert vector has squared
norm equal to the Gibbs variance of its recovered observable. -/
theorem finite_oriented_gibbsHilbert_vacuumCentered_norm_sq_observe
    (L : FiniteOrientedLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    ‖finiteVacuumCentered L.gibbsHilbertVacuum x‖ ^ 2 =
      L.gibbsVarianceReal (L.gibbsHilbertObserveLinearMap x) := by
  calc
    ‖finiteVacuumCentered L.gibbsHilbertVacuum x‖ ^ 2 =
        ‖finiteVacuumCentered L.gibbsHilbertVacuum
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x))‖ ^ 2 := by
              rw [finite_oriented_gibbsHilbert_embed_observe L x]
    _ = L.gibbsVarianceReal (L.gibbsHilbertObserveLinearMap x) :=
      finite_oriented_gibbsHilbert_vacuumCentered_norm_sq
        L (L.gibbsHilbertObserveLinearMap x)

end

end MathlibAnalytic
end MGAP4D
