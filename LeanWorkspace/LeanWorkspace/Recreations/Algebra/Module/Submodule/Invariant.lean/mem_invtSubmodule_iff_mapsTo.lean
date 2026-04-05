import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem mem_invtSubmodule_iff_mapsTo {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ Set.MapsTo f p p := Iff.rfl

alias ⟨_, Module.End.mem_invtSubmodule _root_.Set.Mapsto⟩ := mem_invtSubmodule_iff_mapsTo

