import MGAP4D.MathlibAnalytic.DistinguishedVectorHilbertBasis
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Bases
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

universe u v w

/-- In a separable real Hilbert space every orthonormal family has countable
index type.

The proof uses only the metric geometry of orthonormal vectors and Mathlib's
`Pairwise.countable_of_isOpen_disjoint`: the open radius-`1/2` balls around
distinct orthonormal vectors are pairwise disjoint because their mutual
distance has square `2`. -/
theorem orthonormal_index_countable_of_separable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H]
    {ι : Type v} {e : ι → H}
    (he : Orthonormal ℝ e) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint
      (s := fun i => Metric.ball (e i) (1 / 2 : ℝ))
  · intro i j hij
    change Disjoint
      (Metric.ball (e i) (1 / 2 : ℝ))
      (Metric.ball (e j) (1 / 2 : ℝ))
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hzi' : dist (e i) z < (1 / 2 : ℝ) := by
      rw [dist_comm]
      exact Metric.mem_ball.mp hzi
    have hzj' : dist z (e j) < (1 / 2 : ℝ) :=
      Metric.mem_ball.mp hzj
    have hlt : dist (e i) (e j) < 1 := by
      calc
        dist (e i) (e j) ≤ dist (e i) z + dist z (e j) :=
          dist_triangle _ _ _
        _ < (1 / 2 : ℝ) + (1 / 2 : ℝ) := add_lt_add hzi' hzj'
        _ = 1 := by norm_num
    have hsq : dist (e i) (e j) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real,
        he.norm_eq_one i, he.norm_eq_one j,
        he.inner_eq_zero hij]
      norm_num
    have hnonneg : 0 ≤ dist (e i) (e j) := dist_nonneg
    nlinarith
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨e i, Metric.mem_ball_self (by norm_num)⟩

/-- In particular the index type of any Hilbert basis of a separable real
Hilbert space is countable. -/
theorem hilbertBasis_index_countable_of_separable
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H]
    {ι : Type v} (b : HilbertBasis ι ℝ H) : Countable ι :=
  orthonormal_index_countable_of_separable b.orthonormal

/-- Noncomputably choose the canonical countability witness as an embedding
into `ℕ`. -/
noncomputable def countableIndexEmbeddingToNat
    (ι : Type u) [Countable ι] : ι ↪ ℕ :=
  Classical.choice (nonempty_embedding_nat ι)

/-- Add a distinguished vacuum in front of a countable excitation family. -/
def vacuumOrthogonalSequenceFamily
    {K : Type v} (vacuum : K) (excitation : ℕ → K) : Option ℕ → K
  | none => vacuum
  | some n => excitation n

/-- A unit vacuum together with an orthonormal sequence orthogonal to it forms
an orthonormal `Option ℕ`-family. -/
theorem vacuumOrthogonalSequenceFamily_orthonormal
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (excitation : ℕ → K) (hExcitation : Orthonormal ℝ excitation)
    (hOrthogonal : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0) :
    Orthonormal ℝ (vacuumOrthogonalSequenceFamily vacuum excitation) := by
  constructor
  · intro i
    cases i with
    | none => exact hVacuum
    | some n => exact hExcitation.norm_eq_one n
  · intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some n => simpa [vacuumOrthogonalSequenceFamily] using hOrthogonal n
    | some m =>
        cases j with
        | none =>
            simpa [vacuumOrthogonalSequenceFamily, real_inner_comm] using hOrthogonal m
        | some n =>
            have hmn : m ≠ n := by
              intro h
              apply hij
              simpa [h]
            simpa [vacuumOrthogonalSequenceFamily] using
              hExcitation.inner_eq_zero hmn

/-- Hilbert-basis data generated from a unit vacuum and a countable orthonormal
excitation sequence orthogonal to the vacuum. -/
structure VacuumOrthogonalSequenceHilbertBasisData
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (vacuum : K) (excitation : ℕ → K) where
  Index : Type v
  basis : HilbertBasis Index ℝ K
  vacuumIndex : Index
  sequenceIndex : ℕ ↪ Index
  basis_vacuum : basis vacuumIndex = vacuum
  basis_sequence : ∀ n, basis (sequenceIndex n) = excitation n

/-- Mathlib extends the orthonormal family consisting of the vacuum and its
countable vacuum-orthogonal excitation sequence to a Hilbert basis. -/
theorem vacuumOrthogonalSequenceHilbertBasisData_nonempty
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K]
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (excitation : ℕ → K) (hExcitation : Orthonormal ℝ excitation)
    (hOrthogonal : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0) :
    Nonempty (VacuumOrthogonalSequenceHilbertBasisData vacuum excitation) := by
  classical
  let f : Option ℕ → K := vacuumOrthogonalSequenceFamily vacuum excitation
  have hf : Orthonormal ℝ f :=
    vacuumOrthogonalSequenceFamily_orthonormal
      vacuum hVacuum excitation hExcitation hOrthogonal
  have hs : Orthonormal ℝ ((↑) : Set.range f → K) := hf.toSubtypeRange
  obtain ⟨w, b, hsub, hb⟩ := hs.exists_hilbertBasis_extension
  let iVacuum : w := ⟨vacuum, hsub ⟨none, rfl⟩⟩
  let seq : ℕ → w := fun n => ⟨excitation n, hsub ⟨some n, rfl⟩⟩
  have hSeqInjective : Function.Injective seq := by
    intro m n hmn
    apply hExcitation.linearIndependent.injective
    exact congrArg Subtype.val hmn
  let seqEmbedding : ℕ ↪ w := ⟨seq, hSeqInjective⟩
  refine ⟨{
    Index := w
    basis := b
    vacuumIndex := iVacuum
    sequenceIndex := seqEmbedding
    basis_vacuum := ?_
    basis_sequence := ?_ }⟩
  · exact congr_fun hb iVacuum
  · intro n
    exact congr_fun hb (seqEmbedding n)

/-- Noncomputably selected target Hilbert basis generated from the vacuum and a
vacuum-orthogonal orthonormal excitation sequence. -/
noncomputable def vacuumOrthogonalSequenceHilbertBasisData
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K]
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (excitation : ℕ → K) (hExcitation : Orthonormal ℝ excitation)
    (hOrthogonal : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0) :
    VacuumOrthogonalSequenceHilbertBasisData vacuum excitation :=
  Classical.choice
    (vacuumOrthogonalSequenceHilbertBasisData_nonempty
      vacuum hVacuum excitation hExcitation hOrthogonal)

/-- A separable source Hilbert space embeds isometrically into any target real
Hilbert space carrying a unit distinguished vector and a countable orthonormal
sequence orthogonal to it.  The embedding is theorem-generated and sends the
source distinguished unit vector exactly to the target distinguished vector.

This replaces an opaque Hilbert-cardinal comparison by concrete Hilbert
geometry: source separability plus one vacuum-orthogonal orthonormal sequence in
the target. -/
noncomputable def distinguishedVectorLinearIsometryOfSeparableVacuumOrthogonalSequence
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (x : H) (hx : ‖x‖ = 1)
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (excitation : ℕ → K) (hExcitation : Orthonormal ℝ excitation)
    (hOrthogonal : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0) :
    H →ₗᵢ[ℝ] K := by
  let bH := distinguishedVectorHilbertBasis x hx
  letI : Countable bH.Index :=
    hilbertBasis_index_countable_of_separable bH.basis
  let bK := vacuumOrthogonalSequenceHilbertBasisData
    vacuum hVacuum excitation hExcitation hOrthogonal
  let e : bH.Index ↪ bK.Index :=
    (countableIndexEmbeddingToNat bH.Index).trans bK.sequenceIndex
  exact hilbertBasisLinearIsometryOfEmbedding
    bH.basis bK.basis
    (retargetEmbedding e bH.index bK.vacuumIndex)

/-- The separability/orthonormal-sequence generated isometry preserves the two
distinguished unit vectors exactly. -/
@[simp] theorem distinguishedVectorLinearIsometryOfSeparableVacuumOrthogonalSequence_apply
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (x : H) (hx : ‖x‖ = 1)
    (vacuum : K) (hVacuum : ‖vacuum‖ = 1)
    (excitation : ℕ → K) (hExcitation : Orthonormal ℝ excitation)
    (hOrthogonal : ∀ n, ⟪vacuum, excitation n⟫_ℝ = 0) :
    distinguishedVectorLinearIsometryOfSeparableVacuumOrthogonalSequence
      x hx vacuum hVacuum excitation hExcitation hOrthogonal x = vacuum := by
  let bH := distinguishedVectorHilbertBasis x hx
  letI : Countable bH.Index :=
    hilbertBasis_index_countable_of_separable bH.basis
  let bK := vacuumOrthogonalSequenceHilbertBasisData
    vacuum hVacuum excitation hExcitation hOrthogonal
  let e : bH.Index ↪ bK.Index :=
    (countableIndexEmbeddingToNat bH.Index).trans bK.sequenceIndex
  exact
    hilbertBasisLinearIsometryOfEmbedding_distinguished
      bH.basis bK.basis
      (retargetEmbedding e bH.index bK.vacuumIndex)
      bH.index bK.vacuumIndex x vacuum
      bH.basis_index bK.basis_vacuum
      (retargetEmbedding_apply_distinguished e bH.index bK.vacuumIndex)

end

end MathlibAnalytic
end MGAP4D
