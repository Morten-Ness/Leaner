import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem AffineMap.affineIndependent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    AffineIndependent k (f ∘ p) ↔ AffineIndependent k p := ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

