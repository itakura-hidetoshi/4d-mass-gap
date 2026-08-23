import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSlice
import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteRKHS
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPositiveSemidefiniteCertificate
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProductSpace

noncomputable section

/-- Compact `SU(N)` gauge fields on the canonical time-zero spatial slice of
the modern even-periodic lattice. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
    (H N : ℕ) : Type :=
  PeriodicHypercubicEvenSpatialSliceConfiguration H
    (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Canonical finite ordered list of spatial-slice links. -/
noncomputable def periodicHypercubicEvenSpatialSliceLinkList
    (H : ℕ) : List (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.toList

/-- Canonical finite ordered list of spatial-slice plaquettes. -/
noncomputable def periodicHypercubicEvenSpatialSlicePlaquetteList
    (H : ℕ) : List (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
  classical
  exact Finset.univ.toList

@[simp] theorem periodicHypercubicEvenSpatialSliceLink_mem_list
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    e ∈ periodicHypercubicEvenSpatialSliceLinkList H := by
  classical
  simp [periodicHypercubicEvenSpatialSliceLinkList]

@[simp] theorem periodicHypercubicEvenSpatialSlicePlaquette_mem_list
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    p ∈ periodicHypercubicEvenSpatialSlicePlaquetteList H := by
  classical
  simp [periodicHypercubicEvenSpatialSlicePlaquetteList]

/-- Spatial Wilson action on one canonical time slice. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p =>
    specialUnitaryWilsonPlaquetteEnergy N
      (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)).sum

/-- Restricting a full four-dimensional `SU(N)` configuration recovers exactly
the full Wilson plaquette energy on every embedded spatial-slice plaquette. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_restriction_eq
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (periodicHypercubicEvenSpatialSliceRestriction A) =
      ((periodicHypercubicEvenSpatialSlicePlaquetteList H).map fun p =>
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicPlaquetteHolonomy A
            (periodicHypercubicEvenSpatialSlicePlaquetteEmbedding H p))).sum := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  simp_rw [periodicHypercubicEvenSpatialSlicePlaquetteHolonomy_restriction_eq]

/-- Half of the spatial Boltzmann amplitude assigned to each end of a symmetric
one-slab transfer kernel. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  Real.exp
    (-(beta / 2) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A)

/-- Spatial half-weights are strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  exact Real.exp_pos _

/-- Temporal-gauge Wilson action of one adjacent Euclidean-time slab.  With the
time-like links gauge-fixed to the identity, each temporal plaquette contributes
the relative boundary holonomy `A(e)⁻¹ B(e)`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
    specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e)).sum

/-- Product of the exact local `SU(N)` Wilson relative kernels over all spatial
links in one adjacent-time slab. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
    specialUnitaryWilsonRelativeKernel N beta (A e) (B e)).prod

/-- The finite product of local relative Wilson kernels is exactly the
Boltzmann factor of the temporal-gauge crossing action. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta A B =
      Real.exp (-beta *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
          H N A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih]
      change
        Real.exp
            (-beta * specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e)) *
            Real.exp (-beta *
              (List.map
                (fun e => specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e))
                es).sum) =
          Real.exp (-beta *
            (specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e) +
              (List.map
                (fun e => specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e))
                es).sum))
      rw [← Real.exp_add]
      congr 1
      ring

/-- In particular the actual temporal-gauge crossing kernel is strictly
positive at every pair of spatial boundary configurations. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_pos
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H N beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  exact Real.exp_pos _

/-- Point matrices of a symmetric positive-semidefinite real kernel are
positive-semidefinite matrices. -/
private theorem realKernelPositiveSemidefiniteCertificate_pointMatrix
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealKernelPositiveSemidefiniteCertificate X kernel)
    {ι : Type} [Fintype ι]
    (points : ι → X) :
    Matrix.PosSemidef (fun i j => kernel (points i) (points j)) := by
  let F := C.toHilbertFeature
  have hgram := Matrix.posSemidef_gram ℝ (fun i : ι => F.feature (points i))
  have heq :
      Matrix.gram ℝ (fun i : ι => F.feature (points i)) =
        (fun i j => kernel (points i) (points j)) := by
    ext i j
    exact (F.kernel_eq_inner (points i) (points j)).symm
  rw [heq] at hgram
  exact hgram

/-- For every finite family of spatial boundary configurations, the actual
crossing-kernel point matrix is positive semidefinite.  The proof applies the
Schur product theorem directly to the local `SU(N)` Wilson point matrices. -/
private theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_pointMatrix
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {ι : Type} [Fintype ι]
    (points : ι → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Matrix.PosSemidef
      (fun a b =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
          H N beta (points a) (points b)) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  let C := specialUnitaryWilsonRelativeKernel_positiveSemidefiniteCertificate
    N hN beta hbeta
  induction es with
  | nil =>
      let v : ι → ℝ := fun _ => 1
      have hgram := Matrix.posSemidef_gram ℝ v
      have heq : Matrix.gram ℝ v = (fun _ _ : ι => (1 : ℝ)) := by
        ext i j
        simp [Matrix.gram, v]
      rw [heq] at hgram
      simpa using hgram
  | cons e rest ih =>
      have hhead := realKernelPositiveSemidefiniteCertificate_pointMatrix
        C (fun a : ι => points a e)
      have hprod := hhead.hadamard ih
      simpa only [List.map_cons, List.prod_cons, Matrix.hadamard_apply] using hprod

/-- Symmetry of the full crossing kernel follows link-by-link from symmetry of
the exact local Wilson relative kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta A B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta B A := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
  generalize periodicHypercubicEvenSpatialSliceLinkList H = es
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [specialUnitaryWilsonRelativeKernel_symmetric
        N hN beta hbeta (A e) (B e), ih]

/-- The full temporal crossing kernel is positive semidefinite by the Schur
product theorem applied directly to its finite point matrices. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_positiveSemidefinite
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefinite
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta) := by
  intro ι _ points coefficients
  have hmatrix :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_pointMatrix
      H N hN beta hbeta points
  have hquad := hmatrix.dotProduct_mulVec_nonneg coefficients
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm] using hquad

/-- Complete symmetric-PSD certificate for the full crossing kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelCertificate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefiniteCertificate
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta) where
  symmetric :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_symmetric
      H N hN beta hbeta
  positiveSemidefinite :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_positiveSemidefinite
      H N hN beta hbeta

/-- Lightweight Moore--Aronszajn feature of the full crossing kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelCertificate
    H N hN beta hbeta).toHilbertFeature

/-- The crossing kernel is exactly the inner product of its canonical RKHS
features. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta A B =
      inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
          H N hN beta hbeta).feature A)
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
          H N hN beta hbeta).feature B) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernelFeature
    H N hN beta hbeta).kernel_eq_inner A B

/-- Symmetric complete one-slab Wilson action: half the spatial action on each
boundary plus all temporal crossing plaquettes. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  (1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A +
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B +
    (1 / 2 : ℝ) *
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B

/-- Actual temporal-gauge one-slab Wilson kernel, obtained by sandwiching the
crossing kernel by the two spatial half-Boltzmann amplitudes. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H N beta A B *
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta B

/-- Exact Boltzmann formula for the complete compact `SU(N)` one-slab kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B =
      Real.exp (-beta *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  rw [← Real.exp_add, ← Real.exp_add]
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  congr 1
  ring

/-- The complete one-slab kernel is strictly positive pointwise. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 < periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  exact Real.exp_pos _

/-- Symmetry of the complete one-slab kernel follows from crossing-kernel
symmetry and the symmetric spatial half-weight sandwich. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta B A := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_symmetric
    H N hN beta hbeta A B]
  ring

/-- The spatial half-weight sandwich preserves positive semidefiniteness of the
crossing kernel by absorbing one half-weight into each finite coefficient. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_positiveSemidefinite
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefinite
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta) := by
  intro ι _ points coefficients
  have hcross :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_positiveSemidefinite
      H N hN beta hbeta ι points
        (fun i => coefficients i *
          periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
            H N beta (points i))
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcross

/-- Complete symmetric-PSD certificate for the actual compact one-slab kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelCertificate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealKernelPositiveSemidefiniteCertificate
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta) where
  symmetric :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
      H N hN beta hbeta
  positiveSemidefinite :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_positiveSemidefinite
      H N hN beta hbeta

/-- Canonical Moore--Aronszajn real Hilbert feature of the complete one-slab
compact Wilson kernel.  This avoids the elaboration-heavy explicit dependent
tensor tower while retaining an exact kernel-inner-product identity. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelFeature
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelCertificate
    H N hN beta hbeta).toHilbertFeature

end

end MathlibAnalytic
end MGAP4D