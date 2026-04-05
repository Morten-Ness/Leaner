import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem iSup_induction (S : ι → Subsemigroup M) {C : M → Prop} {x₁ : M} (hx₁ : x₁ ∈ ⨆ i, S i)
    (mem : ∀ i, ∀ x₂ ∈ S i, C x₂) (mul : ∀ x y, C x → C y → C (x * y)) : C x₁ := by
  rw [iSup_eq_closure] at hx₁
  refine closure_induction (fun x₂ hx₂ => ?_) (fun x y _ _ ↦ mul x y) hx₁
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx₂
  exact mem _ _ hi

