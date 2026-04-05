import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem ext_iff_mulSupport : f = g ↔ f.mulSupport = g.mulSupport ∧ ∀ x ∈ f.mulSupport, f x = g x where
  mp h := h ▸ ⟨rfl, fun _ _ ↦ rfl⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ funext fun x ↦ by
    if hx : x ∈ f.mulSupport then exact h₂ x hx
    else rw [Function.notMem_mulSupport.1 hx, Function.notMem_mulSupport.1 (mt (Set.ext_iff.1 h₁ x).2 hx)]

