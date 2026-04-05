import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

theorem map_subtype_mem_of_mem_invtSubmodule {p : Submodule R M} (hp : p ∈ f.invtSubmodule)
    {q : Submodule R p} (hq : q ∈ Module.End.invtSubmodule (LinearMap.restrict f hp)) :
    Submodule.map p.subtype q ∈ f.invtSubmodule := by
  rintro - ⟨⟨x, hx⟩, hx', rfl⟩
  specialize hq hx'
  rw [Submodule.mem_comap, LinearMap.restrict_apply] at hq
  simpa [hq] using hp hx

protected lemma comp {p : Submodule R M} {g : End R M}
    (hf : p ∈ f.invtSubmodule) (hg : p ∈ g.invtSubmodule) :
    p ∈ Module.End.invtSubmodule (f ∘ₗ g) :=
  fun _ hx ↦ hf (hg hx)

