import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem induction_on {motive : (⨁ i, β i) → Prop} (x : ⨁ i, β i) (zero : motive 0)
    (DirectSum.of : ∀ (i : ι) (x : β i), motive (DirectSum.of β i x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  apply DFinsupp.induction x zero
  intro i b f h1 h2 ih
  solve_by_elim

