import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem _root_.Finset.periodic_prod [Add α] [CommMonoid β] {ι : Type*} {f : ι → α → β}
    (s : Finset ι) (hs : ∀ i ∈ s, Function.Periodic (f i) c) : Function.Periodic (∏ i ∈ s, f i) c := s.prod_map_toList f ▸ (s.toList.map f).periodic_prod (by simpa [-Function.Periodic])

