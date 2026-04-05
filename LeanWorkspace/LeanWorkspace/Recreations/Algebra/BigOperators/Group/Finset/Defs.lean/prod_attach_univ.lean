import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_attach_univ [Fintype ι] (f : {i // i ∈ @univ ι _} → M) :
    ∏ i ∈ univ.attach, f i = ∏ i, f ⟨i, mem_univ _⟩ := Fintype.prod_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ <| by simp

