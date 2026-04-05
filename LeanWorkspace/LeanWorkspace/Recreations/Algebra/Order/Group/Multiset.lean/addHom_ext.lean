import Mathlib

variable {α β : Type*}

theorem addHom_ext [AddZeroClass β] ⦃f g : Multiset α →+ β⦄ (h : ∀ x, f {x} = g {x}) : f = g := by
  ext s
  induction s using Multiset.induction_on with
  | empty => simp only [_root_.map_zero]
  | cons a s ih => simp only [← singleton_add, _root_.map_add, ih, h]

