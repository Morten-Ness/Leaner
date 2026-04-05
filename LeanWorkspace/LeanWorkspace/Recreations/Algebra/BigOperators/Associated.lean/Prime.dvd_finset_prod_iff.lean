import Mathlib

variable {ι M M₀ : Type*}

variable {M : Type*} [CommMonoidWithZero M]

theorem Prime.dvd_finset_prod_iff {S : Finset M₀} {p : M} (pp : Prime p) (g : M₀ → M) :
    p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a := ⟨Prime.exists_mem_finset_dvd pp, fun ⟨_, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

