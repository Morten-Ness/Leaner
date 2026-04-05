import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem Units.coe_prod [CommMonoid M] (f : α → Mˣ) (s : Finset α) :
    (↑(∏ i ∈ s, f i) : M) = ∏ i ∈ s, (f i : M) := map_prod (Units.coeHom M) _ _

