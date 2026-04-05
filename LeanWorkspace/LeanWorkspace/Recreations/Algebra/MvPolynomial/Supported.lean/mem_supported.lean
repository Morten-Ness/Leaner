import Mathlib

variable {σ : Type*} {R : Type u}

variable [CommSemiring R] {p : MvPolynomial σ R}

variable {s t : Set σ}

theorem mem_supported : p ∈ MvPolynomial.supported R s ↔ ↑p.vars ⊆ s := by
  classical
  rw [MvPolynomial.supported_eq_range_rename, AlgHom.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    refine _root_.trans (Finset.coe_subset.2 (vars_rename _ _)) ?_
    simp
  · intro hs
    exact exists_rename_eq_of_vars_subset_range p ((↑) : s → σ) Subtype.val_injective (by simpa)

