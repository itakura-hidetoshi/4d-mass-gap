import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSingleLinkHeatBathLinearProjection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The local fluctuation operator `Q_e = I - P_e`, complementary to the exact
single-link heat-bath conditional-expectation projection. -/
noncomputable def FiniteLatticeWilsonSystem.singleLinkHeatBathFluctuationLinearMap
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    (L.Configuration → ℝ) →ₗ[ℝ] (L.Configuration → ℝ) :=
  LinearMap.id - L.singleLinkHeatBathProjectionLinearMap e

@[simp] theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathFluctuationLinearMap e f =
      f - L.singleLinkHeatBathProjectionLinearMap e f :=
  rfl

/-- Conditional expectation annihilates the local fluctuation component. -/
theorem finite_lattice_singleLinkHeatBathProjection_annihilates_fluctuation
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e
        (L.singleLinkHeatBathFluctuationLinearMap e f) = 0 := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply,
    map_sub]
  change L.singleLinkHeatBathProjection e f -
      L.singleLinkHeatBathProjection e
        (L.singleLinkHeatBathProjection e f) = 0
  rw [finite_lattice_singleLinkHeatBathProjection_idempotent]
  simp

/-- The local fluctuation operator annihilates the conditional-expectation
component. -/
theorem finite_lattice_singleLinkHeatBathFluctuation_annihilates_projection
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathFluctuationLinearMap e
        (L.singleLinkHeatBathProjectionLinearMap e f) = 0 := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply]
  change L.singleLinkHeatBathProjection e f -
      L.singleLinkHeatBathProjection e
        (L.singleLinkHeatBathProjection e f) = 0
  rw [finite_lattice_singleLinkHeatBathProjection_idempotent]
  simp

/-- Every observable decomposes into its off-link conditional expectation and
its local fluctuation. -/
theorem finite_lattice_singleLinkHeatBath_projection_add_fluctuation
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathProjectionLinearMap e f +
        L.singleLinkHeatBathFluctuationLinearMap e f = f := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply]
  abel

/-- The complementary local fluctuation operator is itself idempotent. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_idempotent
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    (L.singleLinkHeatBathFluctuationLinearMap e).comp
        (L.singleLinkHeatBathFluctuationLinearMap e) =
      L.singleLinkHeatBathFluctuationLinearMap e := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.comp_apply,
    finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply,
    finite_lattice_singleLinkHeatBathProjection_annihilates_fluctuation]
  simp

/-- The kernel of the fluctuation operator is exactly the range of conditional
expectation. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_ker_eq_projection_range
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    LinearMap.ker (L.singleLinkHeatBathFluctuationLinearMap e) =
      LinearMap.range (L.singleLinkHeatBathProjectionLinearMap e) := by
  ext f
  constructor
  · intro hf
    change L.singleLinkHeatBathFluctuationLinearMap e f = 0 at hf
    rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply] at hf
    have hFix : L.singleLinkHeatBathProjectionLinearMap e f = f :=
      (sub_eq_zero.mp hf).symm
    exact ⟨f, hFix⟩
  · rintro ⟨g, rfl⟩
    change L.singleLinkHeatBathFluctuationLinearMap e
      (L.singleLinkHeatBathProjectionLinearMap e g) = 0
    exact finite_lattice_singleLinkHeatBathFluctuation_annihilates_projection
      L e g

/-- Consequently, the fluctuation kernel is precisely the subspace of
observables depending only on off-link data. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_ker
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    LinearMap.ker (L.singleLinkHeatBathFluctuationLinearMap e) =
      L.offLinkFiberConstantSubmodule e := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_ker_eq_projection_range,
    finite_lattice_singleLinkHeatBathProjectionLinearMap_range]

/-- The range of local fluctuations equals the kernel of conditional
expectation. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_range_eq_projection_ker
    (L : FiniteLatticeWilsonSystem) (e : L.Edge) :
    LinearMap.range (L.singleLinkHeatBathFluctuationLinearMap e) =
      LinearMap.ker (L.singleLinkHeatBathProjectionLinearMap e) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change L.singleLinkHeatBathProjectionLinearMap e
      (L.singleLinkHeatBathFluctuationLinearMap e g) = 0
    exact finite_lattice_singleLinkHeatBathProjection_annihilates_fluctuation
      L e g
  · intro hf
    change L.singleLinkHeatBathProjectionLinearMap e f = 0 at hf
    refine ⟨f, ?_⟩
    rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply, hf]
    simp

/-- Fixed vectors of the fluctuation projection are exactly observables with
zero single-link conditional expectation. -/
theorem finite_lattice_singleLinkHeatBathFluctuationLinearMap_fixed_iff
    (L : FiniteLatticeWilsonSystem)
    (e : L.Edge) (f : L.Configuration → ℝ) :
    L.singleLinkHeatBathFluctuationLinearMap e f = f ↔
      L.singleLinkHeatBathProjectionLinearMap e f = 0 := by
  rw [finite_lattice_singleLinkHeatBathFluctuationLinearMap_apply]
  constructor
  · intro h
    have : -L.singleLinkHeatBathProjectionLinearMap e f = 0 := by
      linarith
    exact neg_eq_zero.mp this
  · intro h
    rw [h]
    simp

end

end MathlibAnalytic
end MGAP4D
