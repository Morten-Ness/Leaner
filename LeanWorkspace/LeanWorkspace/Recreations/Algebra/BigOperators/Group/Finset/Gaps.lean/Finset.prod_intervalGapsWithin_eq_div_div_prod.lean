import Mathlib

variable {α β : Type*} [LinearOrder α] [CommGroup β]
  (F : Finset (α × α)) {k : ℕ} (h : F.card = k) {a b : α}
  (g : α → β)

theorem Finset.prod_intervalGapsWithin_eq_div_div_prod :
    (∏ i ∈ Finset.range (k + 1),
      g (F.intervalGapsWithin h a b i).2 / g (F.intervalGapsWithin h a b i).1) =
    (g b / g a) / ∏ z ∈ F, g z.2 / g z.1 := eq_div_iff_mul_eq'.mpr (F.prod_intervalGapsWithin_mul_prod_eq_div h g)

