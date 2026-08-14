import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalL2Isometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProduct ENNReal NNReal

noncomputable section

universe u

local instance boundaryMarginalInverseNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryMarginalInverseTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryMarginalInverseCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryMarginalInverseSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryMarginalInverseMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryMarginalInverseBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Pointwise square-root-density transport from the interacting boundary
marginal back to boundary Haar.  Since the marginal density is the square of
the strictly positive OS vacuum wavefunction, this is the inverse pointwise
weight to `periodicHypercubicEvenBoundaryHaarToMarginalL2Function`. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalToHaarL2Function
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ℝ :=
  periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b * g b

/-- Square-root-density transport is strongly measurable under boundary Haar. -/
theorem periodicHypercubicEvenBoundaryMarginalToHaarL2Function_aestronglyMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryMarginalToHaarL2Function
        H N hN beta hbeta g)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  exact
    (periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H N hN beta hbeta).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable g).mono_ac
        (periodicHypercubicEvenBoundaryHaarMeasure_absolutelyContinuous_marginalMeasure
          H N hN beta hbeta))

/-- Square-root-density transport of every interacting marginal `L²` vector
belongs to boundary Haar `L²`. -/
theorem periodicHypercubicEvenBoundaryMarginalToHaarL2Function_memLp
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    MemLp
      (periodicHypercubicEvenBoundaryMarginalToHaarL2Function
        H N hN beta hbeta g)
      2
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  apply (memLp_two_iff_integrable_sq
    (periodicHypercubicEvenBoundaryMarginalToHaarL2Function_aestronglyMeasurable
      H N hN beta hbeta g)).2
  let f : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N → ℝ :=
    fun b => (g b) ^ 2
  have hg : Integrable f
      (periodicHypercubicEvenBoundaryMarginalMeasure H N hN beta hbeta) := by
    simpa [f] using (Lp.memLp g).integrable_sq
  rw [periodicHypercubicEvenBoundaryMarginalMeasure_eq_withDensity_nnreal
    H N hN beta hbeta] at hg
  rw [integrable_withDensity_iff_integrable_smul
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal_measurable
      H N hN beta hbeta)] at hg
  apply hg.congr
  filter_upwards with b
  change
    (periodicHypercubicEvenBoundaryMarginalDensityNNReal
        H N hN beta hbeta b : ℝ) * f b =
      (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b * g b) ^ 2
  simp only [f]
  unfold periodicHypercubicEvenBoundaryMarginalDensityNNReal
  simp [Real.coe_toNNReal, sq_nonneg]
  ring

/-- Square-root-density transport as an actual boundary Haar `L²` vector. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalToHaarL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  (periodicHypercubicEvenBoundaryMarginalToHaarL2Function_memLp
    H N hN beta hbeta g).toLp
    (periodicHypercubicEvenBoundaryMarginalToHaarL2Function
      H N hN beta hbeta g)

/-- The Haar representative of square-root-density transport is the expected
pointwise product `ψ * g`. -/
theorem periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryMarginalToHaarL2
      H N hN beta hbeta g =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H N]
      periodicHypercubicEvenBoundaryMarginalToHaarL2Function
        H N hN beta hbeta g :=
  MemLp.coeFn_toLp
    (periodicHypercubicEvenBoundaryMarginalToHaarL2Function_memLp
      H N hN beta hbeta g)

/-- Square-root-density transport preserves addition. -/
theorem periodicHypercubicEvenBoundaryMarginalToHaarL2_add
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g₁ g₂ : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryMarginalToHaarL2
        H N hN beta hbeta (g₁ + g₂) =
      periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g₁ +
        periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g₂ := by
  apply Lp.ext
  have hsource := periodicHypercubicEven_ae_marginal_to_boundaryHaar
    H N hN beta hbeta (Lp.coeFn_add g₁ g₂)
  filter_upwards
    [periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
      H N hN beta hbeta (g₁ + g₂),
      periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
        H N hN beta hbeta g₁,
      periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
        H N hN beta hbeta g₂,
      Lp.coeFn_add
        (periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g₁)
        (periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g₂),
      hsource] with b hsum h₁ h₂ htarget hsrc
  rw [hsum, htarget]
  simp only [Pi.add_apply]
  rw [h₁, h₂]
  unfold periodicHypercubicEvenBoundaryMarginalToHaarL2Function
  rw [hsrc]
  simp only [Pi.add_apply]
  ring

/-- Square-root-density transport preserves real scalar multiplication. -/
theorem periodicHypercubicEvenBoundaryMarginalToHaarL2_smul
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (r : ℝ)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryMarginalToHaarL2
        H N hN beta hbeta (r • g) =
      r • periodicHypercubicEvenBoundaryMarginalToHaarL2
        H N hN beta hbeta g := by
  apply Lp.ext
  have hsource := periodicHypercubicEven_ae_marginal_to_boundaryHaar
    H N hN beta hbeta (Lp.coeFn_smul r g)
  filter_upwards
    [periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
      H N hN beta hbeta (r • g),
      periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
        H N hN beta hbeta g,
      Lp.coeFn_smul r
        (periodicHypercubicEvenBoundaryMarginalToHaarL2
          H N hN beta hbeta g),
      hsource] with b hsmul hg htarget hsrc
  rw [hsmul, htarget]
  simp only [Pi.smul_apply]
  rw [hg]
  unfold periodicHypercubicEvenBoundaryMarginalToHaarL2Function
  rw [hsrc]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Square-root-density boundary transport as a real linear map. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalToHaarL2LinearMap
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N where
  toFun := periodicHypercubicEvenBoundaryMarginalToHaarL2
    H N hN beta hbeta
  map_add' := periodicHypercubicEvenBoundaryMarginalToHaarL2_add
    H N hN beta hbeta
  map_smul' := periodicHypercubicEvenBoundaryMarginalToHaarL2_smul
    H N hN beta hbeta

/-- Reciprocal-vacuum transport after square-root-density transport is the
identity on interacting boundary marginal `L²`. -/
theorem periodicHypercubicEvenBoundaryHaarToMarginalL2_marginalToHaar
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    periodicHypercubicEvenBoundaryHaarToMarginalL2 H N hN beta hbeta
        (periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g) = g := by
  apply Lp.ext
  have hhaar := periodicHypercubicEven_ae_boundaryHaar_to_marginal
    H N hN beta hbeta
    (periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
      H N hN beta hbeta g)
  filter_upwards
    [periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN beta hbeta
      (periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g),
      hhaar] with b hout hin
  rw [hout]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
  rw [hin]
  unfold periodicHypercubicEvenBoundaryMarginalToHaarL2Function
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
  field_simp [ne_of_gt
    (periodicHypercubicEvenBoundaryVacuumMoment_pos H N hN beta hbeta b)]

/-- Square-root-density transport after reciprocal-vacuum transport is the
identity on boundary Haar `L²`. -/
theorem periodicHypercubicEvenBoundaryMarginalToHaarL2_haarToMarginal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenBoundaryHaarL2 H N) :
    periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta
        (periodicHypercubicEvenBoundaryHaarToMarginalL2 H N hN beta hbeta f) = f := by
  apply Lp.ext
  have hmarg := periodicHypercubicEven_ae_marginal_to_boundaryHaar
    H N hN beta hbeta
    (periodicHypercubicEvenBoundaryHaarToMarginalL2_coeFn
      H N hN beta hbeta f)
  filter_upwards
    [periodicHypercubicEvenBoundaryMarginalToHaarL2_coeFn
      H N hN beta hbeta
      (periodicHypercubicEvenBoundaryHaarToMarginalL2 H N hN beta hbeta f),
      hmarg] with b hout hin
  rw [hout]
  unfold periodicHypercubicEvenBoundaryMarginalToHaarL2Function
  rw [hin]
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Function
  unfold periodicHypercubicEvenBoundaryHaarToMarginalL2Weight
  field_simp [ne_of_gt
    (periodicHypercubicEvenBoundaryVacuumMoment_pos H N hN beta hbeta b)]

/-- Square-root-density transport preserves the real `L²` norm exactly. -/
theorem periodicHypercubicEvenBoundaryMarginalToHaarL2_norm
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta) :
    ‖periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g‖ = ‖g‖ := by
  have h := periodicHypercubicEvenBoundaryHaarToMarginalL2_norm
    H N hN beta hbeta
    (periodicHypercubicEvenBoundaryMarginalToHaarL2 H N hN beta hbeta g)
  rw [periodicHypercubicEvenBoundaryHaarToMarginalL2_marginalToHaar
    H N hN beta hbeta g] at h
  exact h.symm

/-- The positive boundary vacuum density change is a real linear isometric
isomorphism from the interacting boundary marginal `L²` onto boundary Haar
`L²`; its inverse is the already-existing reciprocal-vacuum isometry. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalToHaarL2Isometry
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenBoundaryMarginalL2 H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenBoundaryHaarL2 H N :=
  LinearIsometry.mk
    (periodicHypercubicEvenBoundaryMarginalToHaarL2LinearMap
      H N hN beta hbeta)
    (periodicHypercubicEvenBoundaryMarginalToHaarL2_norm
      H N hN beta hbeta)

end

end MathlibAnalytic
end MGAP4D
