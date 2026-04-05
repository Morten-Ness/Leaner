import Mathlib

variable {ι R S : Type*}

theorem PNat.coe_prod {ι : Type*} (f : ι → ℕ+) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : ℕ) := map_prod PNat.coeMonoidHom _ _

