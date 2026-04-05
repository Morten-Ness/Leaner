import Mathlib

variable {α β : Type*}

variable [Sub α] [Bot α]

theorem map_sub [Sub β] [Bot β] {f : α → β} (h : ∀ x y, f (x - y) = f x - f y) (h₀ : f ⊥ = ⊥) :
    ∀ x y : WithTop α, (x - y).map f = x.map f - y.map f
  | _, ⊤ => by simp only [WithTop.sub_top, map_coe, h₀, map_top]
  | ⊤, (x : α) => rfl
  | (x : α), (y : α) => by simp only [← WithTop.coe_sub, map_coe, h]
