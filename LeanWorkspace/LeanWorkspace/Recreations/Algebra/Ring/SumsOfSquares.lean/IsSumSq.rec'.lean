import Mathlib

variable {R : Type*}

theorem IsSumSq.rec' [Mul R] [Add R] [Zero R]
    {motive : (s : R) → (h : IsSumSq s) → Prop}
    (zero : motive 0 zero)
    (sq_add : ∀ {x s}, (hx : IsSquare x) → (hs : IsSumSq s) → motive s hs →
      motive (x + s) (by rcases hx with ⟨_, rfl⟩; exact sq_add _ hs))
    {s : R} (h : IsSumSq s) : motive s h := match h with
  | .zero        => zero
  | .sq_add _ hs => sq_add (.mul_self _) hs (rec' zero sq_add _)

