import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

theorem fold_max_add [LinearOrder M] [Add M] [AddRightMono M] (s : Finset ι) (a : WithBot M)
    (f : ι → M) : s.fold max ⊥ (fun i ↦ ↑(f i) + a) = s.fold max ⊥ ((↑) ∘ f) + a := by
  classical induction s using Finset.induction_on <;> simp [*, max_add_add_right]

