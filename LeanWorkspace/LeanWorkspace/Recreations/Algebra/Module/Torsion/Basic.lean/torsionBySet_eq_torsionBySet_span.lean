import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_eq_torsionBySet_span :
    Submodule.torsionBySet R M s = Submodule.torsionBySet R M (Ideal.span s) := by
  refine le_antisymm (fun x hx => ?_) (Submodule.torsionBySet_le_torsionBySet_of_subset subset_span)
  rw [Submodule.mem_torsionBySet_iff] at hx ⊢
  suffices Ideal.span s ≤ Ideal.torsionOf R M x by
    rintro ⟨a, ha⟩
    exact this ha
  rw [Ideal.span_le]
  exact fun a ha => hx ⟨a, ha⟩

