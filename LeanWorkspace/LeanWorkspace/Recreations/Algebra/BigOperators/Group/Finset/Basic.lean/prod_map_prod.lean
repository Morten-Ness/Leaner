import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem prod_map_prod {α : Type*} [CommMonoid M] {m : Multiset ι} {s : Finset α} {f : ι → α → M} :
    (m.map fun i ↦ ∏ a ∈ s, f i a).prod = ∏ a ∈ s, (m.map fun i ↦ f i a).prod := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, prod_map_mul, ih]

