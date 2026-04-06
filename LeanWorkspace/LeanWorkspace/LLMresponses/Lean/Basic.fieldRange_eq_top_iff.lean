import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem fieldRange_eq_top_iff {f : K →+* L} :
    f.fieldRange = ⊤ ↔ Function.Surjective f := by
  constructor
  · intro h
    intro y
    have hy : y ∈ f.fieldRange := by
      rw [h]
      simp
    rcases hy with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · intro h
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      rcases h y with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
