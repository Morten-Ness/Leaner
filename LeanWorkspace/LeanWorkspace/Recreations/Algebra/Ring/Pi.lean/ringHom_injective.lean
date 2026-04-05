import Mathlib

variable {I : Type u}

variable {f : I → Type v}

variable (i : I)

theorem ringHom_injective {γ : Type w} [Nonempty I] [∀ i, NonAssocSemiring (f i)]
    [NonAssocSemiring γ] (g : ∀ i, γ →+* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.ringHom g) := monoidHom_injective (fun i => (g i).toMonoidHom) hg

