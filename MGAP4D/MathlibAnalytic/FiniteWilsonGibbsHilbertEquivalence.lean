import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHilbertRealization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Every finite Wilson Gibbs configuration has strictly positive real
probability.  This is the finite-volume full-support property needed to invert
multiplication by the square root of the Gibbs density. -/
theorem finite_lattice_gibbsProbabilityReal_pos
    (L : FiniteLatticeWilsonSystem) (A : L.Configuration) :
    0 < L.gibbsProbabilityReal A := by
  unfold FiniteLatticeWilsonSystem.gibbsProbabilityReal
  apply ENNReal.toReal_pos
  · rw [finite_lattice_gibbsPMF_apply]
    exact mul_ne_zero
      (finite_lattice_boltzmannWeight_ne_zero L A)
      (ENNReal.inv_ne_zero.mpr
        (finite_lattice_partitionFunction_ne_top L))
  · exact L.gibbsPMF.apply_ne_top A

/-- The square root of every finite Wilson Gibbs probability is nonzero. -/
theorem finite_lattice_sqrt_gibbsProbabilityReal_ne_zero
    (L : FiniteLatticeWilsonSystem) (A : L.Configuration) :
    Real.sqrt (L.gibbsProbabilityReal A) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (finite_lattice_gibbsProbabilityReal_pos L A))

/-- Recover the underlying observable from its Euclidean Gibbs Hilbert vector
by dividing pointwise by `sqrt(mu)`. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsHilbertObserveLinearMap
    (L : FiniteLatticeWilsonSystem) :
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

@[simp] theorem finite_lattice_gibbsHilbertObserveLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) (A : L.Configuration) :
    L.gibbsHilbertObserveLinearMap x A =
      x A / Real.sqrt (L.gibbsProbabilityReal A) :=
  rfl

/-- Observing an embedded finite Wilson observable recovers the observable. -/
theorem finite_lattice_gibbsHilbert_observe_embed
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsHilbertObserveLinearMap
        (L.gibbsHilbertEmbedLinearMap f) = f := by
  funext A
  rw [finite_lattice_gibbsHilbertObserveLinearMap_apply,
    finite_lattice_gibbsHilbertEmbedLinearMap_apply]
  field_simp [finite_lattice_sqrt_gibbsProbabilityReal_ne_zero L A]

/-- Embedding the observable recovered from a Gibbs Hilbert vector returns the
original vector. -/
theorem finite_lattice_gibbsHilbert_embed_observe
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    L.gibbsHilbertEmbedLinearMap
        (L.gibbsHilbertObserveLinearMap x) = x := by
  ext A
  rw [finite_lattice_gibbsHilbertEmbedLinearMap_apply,
    finite_lattice_gibbsHilbertObserveLinearMap_apply]
  field_simp [finite_lattice_sqrt_gibbsProbabilityReal_ne_zero L A]

/-- Multiplication by `sqrt(mu)` is a linear equivalence from finite Wilson
observables to the concrete Euclidean Gibbs Hilbert space. -/
noncomputable def FiniteLatticeWilsonSystem.gibbsHilbertLinearEquiv
    (L : FiniteLatticeWilsonSystem) :
    (L.Configuration → ℝ) ≃ₗ[ℝ] L.GibbsHilbertSpace :=
  LinearEquiv.ofBijective L.gibbsHilbertEmbedLinearMap
    ⟨by
      intro f g hfg
      calc
        f = L.gibbsHilbertObserveLinearMap
            (L.gibbsHilbertEmbedLinearMap f) :=
          (finite_lattice_gibbsHilbert_observe_embed L f).symm
        _ = L.gibbsHilbertObserveLinearMap
            (L.gibbsHilbertEmbedLinearMap g) := by
          exact congrArg
            (fun x : L.GibbsHilbertSpace =>
              L.gibbsHilbertObserveLinearMap x) hfg
        _ = g := finite_lattice_gibbsHilbert_observe_embed L g,
    by
      intro x
      exact ⟨L.gibbsHilbertObserveLinearMap x,
        finite_lattice_gibbsHilbert_embed_observe L x⟩⟩

/-- For an arbitrary vector in the concrete Gibbs Hilbert carrier, vacuum
centering has squared norm equal to the Gibbs variance of its recovered
observable. -/
theorem finite_lattice_gibbsHilbert_vacuumCentered_norm_sq_observe
    (L : FiniteLatticeWilsonSystem)
    (x : L.GibbsHilbertSpace) :
    ‖finiteVacuumCentered L.gibbsHilbertVacuum x‖ ^ 2 =
      L.gibbsVarianceReal (L.gibbsHilbertObserveLinearMap x) := by
  calc
    ‖finiteVacuumCentered L.gibbsHilbertVacuum x‖ ^ 2 =
        ‖finiteVacuumCentered L.gibbsHilbertVacuum
          (L.gibbsHilbertEmbedLinearMap
            (L.gibbsHilbertObserveLinearMap x))‖ ^ 2 := by
              rw [finite_lattice_gibbsHilbert_embed_observe L x]
    _ = L.gibbsVarianceReal (L.gibbsHilbertObserveLinearMap x) :=
      finite_lattice_gibbsHilbert_vacuumCentered_norm_sq
        L (L.gibbsHilbertObserveLinearMap x)

end

end MathlibAnalytic
end MGAP4D
