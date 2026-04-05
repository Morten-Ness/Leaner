import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι] {α : ι → Type u} {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

theorem sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i) :
    DirectSum.sigmaCurry f i j = f ⟨i, j⟩ := DFinsupp.sigmaCurry_apply (δ := δ) _ i j

