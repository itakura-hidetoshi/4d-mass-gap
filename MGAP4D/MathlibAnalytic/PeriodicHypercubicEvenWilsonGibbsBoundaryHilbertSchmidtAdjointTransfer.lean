import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryHilbertSchmidtAnalysis
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance boundaryHilbertSchmidtAdjointSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryHilbertSchmidtAdjointSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryHilbertSchmidtAdjointSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryHilbertSchmidtAdjointSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryHilbertSchmidtAdjointSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryHilbertSchmidtAdjointSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The synthesis map associated with the actual Wilson Hilbert--Schmidt
analysis is not independent data: it is canonically its Hilbert adjoint. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryHilbertSchmidtSynthesis
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N :=
  ContinuousLinearMap.adjoint
    (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAnalysis
      H N hN beta hbeta)

/-- Canonical positive shared-boundary transfer candidate generated entirely by
the actual Wilson compact-Haar kernel:

`K = A† A`.

The remaining Yang--Mills-specific obligation is to identify this canonical
operator with the boundary moment of one genuine lattice-time translation. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N :=
  (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtSynthesis
    H N hN beta hbeta).comp
      (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAnalysis
        H N hN beta hbeta)

/-- The quadratic form of the canonical boundary transfer is exactly the
squared norm of the actual Wilson analysis feature.  Positivity is therefore a
theorem, not an additional transfer hypothesis. -/
theorem periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer_inner_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
          H N hN beta hbeta f) f =
      ‖periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAnalysis
          H N hN beta hbeta f‖ ^ 2 := by
  let A := periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAnalysis
    H N hN beta hbeta
  change inner ℝ ((ContinuousLinearMap.adjoint A) (A f)) f = ‖A f‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact real_inner_self_eq_norm_sq (A f)

/-- Hence the canonical actual-kernel boundary transfer has nonnegative
quadratic form on every shared-boundary `L²` state. -/
theorem periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer_inner_self_nonneg
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
        H N hN beta hbeta f) f := by
  rw [periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer_inner_self]
  exact sq_nonneg _

/-- Matrix coefficients of the canonical `A† A` transfer reduce to matrix
coefficients in the actual open-half feature Hilbert space. -/
theorem periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
          H N hN beta hbeta f) g =
      inner ℝ
        (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAnalysis
          H N hN beta hbeta f)
        (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAnalysis
          H N hN beta hbeta g) := by
  let A := periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAnalysis
    H N hN beta hbeta
  change inner ℝ ((ContinuousLinearMap.adjoint A) (A f)) g =
    inner ℝ (A f) (A g)
  exact ContinuousLinearMap.adjoint_inner_left A g (A f)

/-- The canonical transfer is symmetric. -/
theorem periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer_symmetric
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 H N) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
          H N hN beta hbeta f) g =
      inner ℝ f
        (periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer
          H N hN beta hbeta g) := by
  rw [periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer_inner,
    real_inner_comm,
    periodicHypercubicEvenWilsonBoundaryHilbertSchmidtAdjointTransfer_inner]

end

end MathlibAnalytic
end MGAP4D
