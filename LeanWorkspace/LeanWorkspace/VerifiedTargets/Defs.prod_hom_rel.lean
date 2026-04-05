import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_hom_rel [CommMonoid N] {r : M → N → Prop} {f : ι → M} {g : ι → N} {s : Finset ι}
    (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) :
    r (∏ x ∈ s, f x) (∏ x ∈ s, g x) := by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption

