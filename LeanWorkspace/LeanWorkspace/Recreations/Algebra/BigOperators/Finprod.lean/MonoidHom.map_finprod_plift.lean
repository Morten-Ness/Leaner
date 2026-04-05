import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem MonoidHom.map_finprod_plift (f : M →* N) (g : α → M)
    (h : HasFiniteMulSupport <| g ∘ PLift.down) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) := by
  rw [finprod_eq_prod_plift_of_mulSupport_subset h.coe_toFinset.ge,
    finprod_eq_prod_plift_of_mulSupport_subset, map_prod]
  rw [h.coe_toFinset]
  exact mulSupport_comp_subset f.map_one (g ∘ PLift.down)

