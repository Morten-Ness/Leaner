import Mathlib

variable {ι M N : Type*}

variable [Monoid M] [Monoid N]

theorem prod_hom_rel (l : List ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
    (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) : r (l.map f).prod (l.map g).prod := List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]

