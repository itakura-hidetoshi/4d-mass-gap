import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace LinearPMap

noncomputable section

universe u

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A B : E →ₗ.[ℝ] E}

/-- A point in the domain of a partial linear operator is also a domain point of
any graph extension. -/
def domainPointOfLE (h : A ≤ B) (x : A.domain) : B.domain :=
  ⟨x, h.1 x.property⟩

@[simp] theorem coe_domainPointOfLE
    (h : A ≤ B) (x : A.domain) :
    ((domainPointOfLE h x : B.domain) : E) = (x : E) :=
  rfl

/-- Graph extension preserves the operator value on every original domain
point. -/
theorem apply_domainPointOfLE
    (h : A ≤ B) (x : A.domain) :
    B (domainPointOfLE h x) = A x := by
  symm
  exact h.2 rfl

end

end LinearPMap
