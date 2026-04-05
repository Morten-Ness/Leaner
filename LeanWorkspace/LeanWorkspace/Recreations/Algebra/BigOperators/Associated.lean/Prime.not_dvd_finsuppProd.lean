import Mathlib

variable {ι M M₀ : Type*}

variable {M : Type*} [CommMonoidWithZero M]

theorem Prime.not_dvd_finsuppProd {f : M₀ →₀ M} {g : M₀ → M → ℕ} {p : ℕ} (pp : Prime p)
    (hS : ∀ a ∈ f.support, ¬p ∣ g a (f a)) : ¬p ∣ f.prod g := Prime.not_dvd_finset_prod pp hS

