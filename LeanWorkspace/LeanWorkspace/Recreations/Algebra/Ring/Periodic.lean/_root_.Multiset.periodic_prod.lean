import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem _root_.Multiset.periodic_prod [Add α] [CommMonoid β] (s : Multiset (α → β))
    (hs : ∀ f ∈ s, Function.Periodic f c) : Function.Periodic s.prod c := (s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f <| Multiset.mem_toList.mp hf

