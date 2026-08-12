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

end RealKernelPositiveSemidefiniteCertificate

end

end MathlibAnalytic
end MGAP4D
