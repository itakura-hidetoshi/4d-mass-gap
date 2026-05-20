import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairTransportScaffold

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Concrete `l2` addition on the subtype carrier.  This is defined explicitly
because `ConcreteL2RealSequence` is a square-summable subtype, not an inherited
normed-space structure. -/
def concreteL2RealAdd (x y : ConcreteL2RealSequence) : ConcreteL2RealSequence :=
  ⟨fun n : ℕ => x.1 n + y.1 n, by
    have hsumBound :
        Summable fun n : ℕ =>
          (2 : ℝ) • ((x.1 n) ^ 2) + (2 : ℝ) • ((y.1 n) ^ 2) := by
      exact (x.2.const_smul (2 : ℝ)).add (y.2.const_smul (2 : ℝ))
    refine Summable.of_nonneg_of_le ?hNonneg ?hLe hsumBound
    · intro n
      exact sq_nonneg (x.1 n + y.1 n)
    · intro n
      simpa [two_smul] using
        concrete_l2_r2_sq_add_le_two_sq_add_two_sq (x.1 n) (y.1 n)⟩

/-- Concrete scalar multiplication on the square-summable subtype carrier. -/
def concreteL2RealSmul (c : ℝ) (x : ConcreteL2RealSequence) : ConcreteL2RealSequence :=
  ⟨fun n : ℕ => c * x.1 n, by
    have hseq :
        (fun n : ℕ => (c * x.1 n) ^ 2) =
          (fun n : ℕ => (c ^ 2) • ((x.1 n) ^ 2)) := by
      funext n
      simp [pow_two]
      ring
    rw [hseq]
    exact x.2.const_smul (c ^ 2)⟩

/-- Pointwise zero law for concrete `l2` addition. -/
theorem concrete_l2_real_add_zero_ext (x : ConcreteL2RealSequence) (n : ℕ) :
    (concreteL2RealAdd x concreteL2RealZero).1 n = x.1 n := by
  simp [concreteL2RealAdd, concreteL2RealZero]

/-- Pointwise zero law for concrete `l2` scalar multiplication. -/
theorem concrete_l2_real_smul_one_ext (x : ConcreteL2RealSequence) (n : ℕ) :
    (concreteL2RealSmul (1 : ℝ) x).1 n = x.1 n := by
  simp [concreteL2RealSmul]

/-- Zero pair in the concrete graph pair space. -/
def concreteL2GraphPairZero : ConcreteL2GraphPairSpace :=
  (concreteL2RealZero, concreteL2RealZero)

/-- Addition in the concrete graph pair space, using explicit subtype addition. -/
def concreteL2GraphPairAdd
    (p q : ConcreteL2GraphPairSpace) : ConcreteL2GraphPairSpace :=
  (concreteL2RealAdd p.1 q.1, concreteL2RealAdd p.2 q.2)

/-- Scalar multiplication in the concrete graph pair space, using explicit subtype
scalar multiplication. -/
def concreteL2GraphPairSmul
    (c : ℝ) (p : ConcreteL2GraphPairSpace) : ConcreteL2GraphPairSpace :=
  (concreteL2RealSmul c p.1, concreteL2RealSmul c p.2)

/-- First projection is compatible with graph-pair addition. -/
theorem concrete_l2_graph_pair_fst_add
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairFst (concreteL2GraphPairAdd p q) =
      concreteL2RealAdd (concreteL2GraphPairFst p) (concreteL2GraphPairFst q) := by
  rfl

/-- Second projection is compatible with graph-pair addition. -/
theorem concrete_l2_graph_pair_snd_add
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSnd (concreteL2GraphPairAdd p q) =
      concreteL2RealAdd (concreteL2GraphPairSnd p) (concreteL2GraphPairSnd q) := by
  rfl

/-- First projection is compatible with graph-pair scalar multiplication. -/
theorem concrete_l2_graph_pair_fst_smul
    (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairFst (concreteL2GraphPairSmul c p) =
      concreteL2RealSmul c (concreteL2GraphPairFst p) := by
  rfl

/-- Second projection is compatible with graph-pair scalar multiplication. -/
theorem concrete_l2_graph_pair_snd_smul
    (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSnd (concreteL2GraphPairSmul c p) =
      concreteL2RealSmul c (concreteL2GraphPairSnd p) := by
  rfl

/-- Zero is the neutral graph pair at the projection level. -/
theorem concrete_l2_graph_pair_zero_fst :
    concreteL2GraphPairFst concreteL2GraphPairZero = concreteL2RealZero := by
  rfl

/-- Zero is the neutral graph pair at the projection level. -/
theorem concrete_l2_graph_pair_zero_snd :
    concreteL2GraphPairSnd concreteL2GraphPairZero = concreteL2RealZero := by
  rfl

/-- R2i graph-pair linear scaffold.  This creates explicit add/smul operations on
`ConcreteL2RealSequence` and on graph pairs, preparing later graph-norm topology
work.  It does not yet assert that the diagonal graph carrier is closed under
these operations. -/
structure ConcreteL2R2GraphPairLinearScaffold where
  r2hReady : concreteAnalyticSpineL2R2GraphPairTransportScaffoldReady
  realAdd : ConcreteL2RealSequence → ConcreteL2RealSequence → ConcreteL2RealSequence
  realSmul : ℝ → ConcreteL2RealSequence → ConcreteL2RealSequence
  pairZero : ConcreteL2GraphPairSpace
  pairAdd : ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace
  pairSmul : ℝ → ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace
  fstAddLaw : ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphPairFst (pairAdd p q) =
      realAdd (concreteL2GraphPairFst p) (concreteL2GraphPairFst q)
  sndAddLaw : ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphPairSnd (pairAdd p q) =
      realAdd (concreteL2GraphPairSnd p) (concreteL2GraphPairSnd q)
  fstSmulLaw : ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairFst (pairSmul c p) =
      realSmul c (concreteL2GraphPairFst p)
  sndSmulLaw : ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairSnd (pairSmul c p) =
      realSmul c (concreteL2GraphPairSnd p)
  boundaryNotDiagonalGraphAddClosure : Prop
  boundaryNotDiagonalGraphSmulClosure : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2i graph-pair linear scaffold. -/
def concreteL2R2GraphPairLinearScaffold :
    ConcreteL2R2GraphPairLinearScaffold :=
  { r2hReady := concrete_analytic_spine_l2_r2_graph_pair_transport_scaffold_ready
    realAdd := concreteL2RealAdd
    realSmul := concreteL2RealSmul
    pairZero := concreteL2GraphPairZero
    pairAdd := concreteL2GraphPairAdd
    pairSmul := concreteL2GraphPairSmul
    fstAddLaw := concrete_l2_graph_pair_fst_add
    sndAddLaw := concrete_l2_graph_pair_snd_add
    fstSmulLaw := concrete_l2_graph_pair_fst_smul
    sndSmulLaw := concrete_l2_graph_pair_snd_smul
    boundaryNotDiagonalGraphAddClosure := True
    boundaryNotDiagonalGraphSmulClosure := True
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2i graph-pair linear scaffold readiness. -/
def concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairTransportScaffoldReady ∧
  Nonempty (ConcreteL2RealSequence → ConcreteL2RealSequence → ConcreteL2RealSequence) ∧
  Nonempty (ℝ → ConcreteL2RealSequence → ConcreteL2RealSequence) ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotDiagonalGraphAddClosure ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotDiagonalGraphSmulClosure ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotGraphNormDensityTheorem ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairLinearScaffold.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2i graph-pair linear scaffold. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_linear_scaffold_ready :
    concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady := by
  unfold concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_transport_scaffold_ready <|
      And.intro ⟨concreteL2RealAdd⟩ <|
        And.intro ⟨concreteL2RealSmul⟩ <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for R2i graph-pair linear scaffold. -/
def concreteAnalyticSpineL2R2GraphPairLinearHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady

/-- Boundary theorem for R2i graph-pair linear scaffold. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_linear_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairLinearHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_linear_scaffold_ready

end

end MathlibAnalytic
end MGAP4D
