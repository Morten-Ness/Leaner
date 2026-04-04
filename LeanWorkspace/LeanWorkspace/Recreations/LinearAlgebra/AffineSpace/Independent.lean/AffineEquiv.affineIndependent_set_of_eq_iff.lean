import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem AffineEquiv.affineIndependent_set_of_eq_iff {s : Set P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k ((↑) : e '' s → P₂) ↔ AffineIndependent k ((↑) : s → P) := by
  have : e ∘ ((↑) : s → P) = ((↑) : e '' s → P₂) ∘ (e : P ≃ P₂).image s := rfl
  simp [← e.affineIndependent_iff, this, affineIndependent_equiv]

