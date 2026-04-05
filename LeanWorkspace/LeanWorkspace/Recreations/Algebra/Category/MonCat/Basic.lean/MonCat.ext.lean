import Mathlib

theorem ext {X Y : MonCat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g := ConcreteCategory.hom_ext _ _ w

