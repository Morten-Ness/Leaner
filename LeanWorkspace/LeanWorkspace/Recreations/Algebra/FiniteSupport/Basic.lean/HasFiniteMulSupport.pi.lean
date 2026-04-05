import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.pi {ι : Type*} [Finite α] {f : ι → α → M}
    (hf : ∀ a, HasFiniteMulSupport (f · a)) :
    HasFiniteMulSupport f := by
  simp only [HasFiniteMulSupport] at hf ⊢
  refine (Set.finite_iUnion hf).subset fun i hi ↦ ?_
  simp only [mem_mulSupport, Set.mem_iUnion] at hi ⊢
  exact ne_iff.mp hi

