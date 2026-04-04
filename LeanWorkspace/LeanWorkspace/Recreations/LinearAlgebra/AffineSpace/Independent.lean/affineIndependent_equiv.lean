import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι') {p : ι' → P} :
    AffineIndependent k (p ∘ e) ↔ AffineIndependent k p := by
  refine ⟨?_, AffineIndependent.comp_embedding e.toEmbedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.toEmbedding := by
    ext
    simp
  rw [this]
  exact h.comp_embedding e.symm.toEmbedding

