import Mathlib

variable {α β M N : Type*}

variable {G : Type*} [Group G] {s t : Set α}

theorem mulIndicator_inv' (s : Set α) (f : α → G) : mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹ := (Set.mulIndicatorHom G s).map_inv f

