import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem MonoidHom.map_finprod_mem' {f : α → M} (g : M →* N) (h₀ : (s ∩ mulSupport f).Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) := by
  rw [map_finprod g]
  · simp only [g.map_finprod_Prop]
  · simpa only [finprod_eq_mulIndicator_apply, HasFiniteMulSupport, mulSupport_mulIndicator]

