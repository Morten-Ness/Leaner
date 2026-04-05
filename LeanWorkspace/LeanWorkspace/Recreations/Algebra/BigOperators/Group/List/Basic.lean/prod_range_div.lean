import Mathlib

variable {ι α β M N P G : Type*}

variable [CommGroup G]

theorem prod_range_div (n : ℕ) (f : ℕ → G) :
    ((range n).map fun k ↦ f (k + 1) / f k).prod = f n / f 0 := by
  have h : ((·⁻¹) ∘ fun k ↦ f (k + 1) / f k) = fun k ↦ f k / f (k + 1) := by ext; apply inv_div
  rw [← inv_inj, List.prod_inv, map_map, inv_div, h, List.prod_range_div']

