import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subtype_map_embedding {p : ι → Prop} {s : Finset { x // p x }} {f : { x // p x } → M}
    {g : ι → M} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x ∈ s.map (Function.Embedding.subtype _), g x) = ∏ x ∈ s, f x := by
  classical
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h
