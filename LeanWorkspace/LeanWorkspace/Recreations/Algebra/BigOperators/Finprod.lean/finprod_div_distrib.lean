import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_div_distrib [DivisionCommMonoid G] {f g : α → G} (hf : HasFiniteMulSupport f)
    (hg : HasFiniteMulSupport g) : ∏ᶠ i, f i / g i = (∏ᶠ i, f i) / ∏ᶠ i, g i := by
  simp only [div_eq_mul_inv, finprod_mul_distrib hf <| hg.fun_inv, finprod_inv_distrib]

