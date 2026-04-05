import Mathlib

variable {ι M M₀ : Type*}

variable {M : Type*} [CommMonoidWithZero M]

theorem Prime.dvd_finsuppProd_iff {f : M₀ →₀ M} {g : M₀ → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) := Prime.dvd_finset_prod_iff pp _

