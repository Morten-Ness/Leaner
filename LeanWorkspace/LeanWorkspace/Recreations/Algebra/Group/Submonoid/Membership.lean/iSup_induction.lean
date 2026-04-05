import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem iSup_induction {ι : Sort*} (S : ι → Submonoid M) {motive : M → Prop} {x : M}
    (hx : x ∈ ⨆ i, S i) (mem : ∀ (i), ∀ x ∈ S i, motive x) (one : motive 1)
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive x := by
  rw [iSup_eq_closure] at hx
  refine closure_induction (fun x hx => ?_) one (fun _ _ _ _ ↦ mul _ _) hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact mem _ _ hi

