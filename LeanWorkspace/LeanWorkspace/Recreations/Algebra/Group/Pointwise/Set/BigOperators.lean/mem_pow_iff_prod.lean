import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem mem_pow_iff_prod {n : ℕ} {s : Set α} {a : α} :
    a ∈ s ^ n ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ ∏ i, f i = a := by
  simpa using Set.mem_finset_prod (t := .univ) (f := fun _ : Fin n ↦ s) _

