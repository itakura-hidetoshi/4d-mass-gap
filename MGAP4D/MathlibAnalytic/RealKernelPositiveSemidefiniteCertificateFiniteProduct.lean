import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteCertificateAlgebra

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace RealKernelPositiveSemidefiniteCertificate

/-- The constant-one kernel is symmetric positive semidefinite. -/
noncomputable def one
    (X : Type) :
    RealKernelPositiveSemidefiniteCertificate X (fun _ _ => 1) :=
  (RealHilbertKernelFeature.one X).toPositiveSemidefiniteCertificate

/-- Any finite Schur product of symmetric positive-semidefinite kernels is
symmetric positive semidefinite.  The proof iterates Hilbert tensor products,
so the result remains a genuine Hilbert-kernel statement rather than a
matrix-only closure lemma. -/
theorem finsetProd
    {X ι : Type}
    (s : Finset ι)
    (kernel : ι → X → X → ℝ)
    (C : ∀ i ∈ s, RealKernelPositiveSemidefiniteCertificate X (kernel i)) :
    RealKernelPositiveSemidefiniteCertificate X
      (fun x y => ∏ i ∈ s, kernel i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using RealKernelPositiveSemidefiniteCertificate.one X
  | @insert a s ha ih =>
      have Ca : RealKernelPositiveSemidefiniteCertificate X (kernel a) :=
        C a (by simp)
      have Cs : RealKernelPositiveSemidefiniteCertificate X
          (fun x y => ∏ i ∈ s, kernel i x y) :=
        ih (fun i hi => C i (by simp [hi]))
      simpa [Finset.prod_insert, ha] using Ca.mul Cs

/-- Finite-product PSD domination.  If every exact factor and every selected
factor is PSD, and deleting the selected factor from each exact factor leaves
a PSD remainder, then the full product minus the product of all selected
factors is PSD.

The induction is the cancellation-free telescoping identity
`Fₐ F - Sₐ S = (Fₐ-Sₐ)F + Sₐ(F-S)`; each summand is a Schur product of PSD
kernels. -/
theorem finsetProd_sub_finsetProd
    {X ι : Type}
    (s : Finset ι)
    (full selected : ι → X → X → ℝ)
    (Cfull : ∀ i ∈ s,
      RealKernelPositiveSemidefiniteCertificate X (full i))
    (Cselected : ∀ i ∈ s,
      RealKernelPositiveSemidefiniteCertificate X (selected i))
    (Cremainder : ∀ i ∈ s,
      RealKernelPositiveSemidefiniteCertificate X
        (fun x y => full i x y - selected i x y)) :
    RealKernelPositiveSemidefiniteCertificate X
      (fun x y =>
        (∏ i ∈ s, full i x y) -
          ∏ i ∈ s, selected i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using RealKernelPositiveSemidefiniteCertificate.zero X
  | @insert a s ha ih =>
      have CfullA : RealKernelPositiveSemidefiniteCertificate X (full a) :=
        Cfull a (by simp)
      have CselectedA : RealKernelPositiveSemidefiniteCertificate X (selected a) :=
        Cselected a (by simp)
      have CremainderA : RealKernelPositiveSemidefiniteCertificate X
          (fun x y => full a x y - selected a x y) :=
        Cremainder a (by simp)
      have CfullTail : RealKernelPositiveSemidefiniteCertificate X
          (fun x y => ∏ i ∈ s, full i x y) :=
        finsetProd s full (fun i hi => Cfull i (by simp [hi]))
      have CremainderTail : RealKernelPositiveSemidefiniteCertificate X
          (fun x y =>
            (∏ i ∈ s, full i x y) -
              ∏ i ∈ s, selected i x y) :=
        ih
          (fun i hi => Cfull i (by simp [hi]))
          (fun i hi => Cselected i (by simp [hi]))
          (fun i hi => Cremainder i (by simp [hi]))
      have Ctelescoping :=
        (CremainderA.mul CfullTail).add
          (CselectedA.mul CremainderTail)
      have hkernel :
          (fun x y =>
            (∏ i ∈ insert a s, full i x y) -
              ∏ i ∈ insert a s, selected i x y) =
          (fun x y =>
            (full a x y - selected a x y) *
                (∏ i ∈ s, full i x y) +
              selected a x y *
                ((∏ i ∈ s, full i x y) -
                  ∏ i ∈ s, selected i x y)) := by
        funext x y
        simp [Finset.prod_insert, ha]
        ring
      rw [hkernel]
      exact Ctelescoping

end RealKernelPositiveSemidefiniteCertificate

end

end MathlibAnalytic
end MGAP4D
