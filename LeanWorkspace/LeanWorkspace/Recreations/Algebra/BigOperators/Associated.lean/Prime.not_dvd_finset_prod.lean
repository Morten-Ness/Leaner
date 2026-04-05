import Mathlib

variable {ι M M₀ : Type*}

variable {M : Type*} [CommMonoidWithZero M]

theorem Prime.not_dvd_finset_prod {S : Finset M₀} {p : M} (pp : Prime p) {g : M₀ → M}
    (hS : ∀ a ∈ S, ¬p ∣ g a) : ¬p ∣ S.prod g := by
  exact mt (Prime.dvd_finset_prod_iff pp _).1 <| not_exists.2 fun a => not_and.2 (hS a)

