import Mathlib

variable {M : Type*}

theorem coe_closure [Semigroup M] {s : Set M} :
    (closure s : Set M) = s ∪ Set.univ * s := by
  let I : SemigroupIdeal M :=
    { carrier := s ∪ Set.univ * s
      smul_mem' x y := by
        rintro (hy | ⟨y, -, z, hz, rfl⟩)
        · exact .inr <| mul_mem_mul (mem_univ _) hy
        · simpa [← mul_assoc] using .inr <| mul_mem_mul (mem_univ _) hz }
  suffices closure s = I by rw [this]; rfl
  refine (SemigroupIdeal.closure_le.2 fun x => Or.inl).antisymm fun x hx => hx.elim SemigroupIdeal.mem_closure_of_mem ?_
  rintro ⟨y, -, z, hz, rfl⟩
  exact SemigroupIdeal.mul_mem _ _ (SemigroupIdeal.mem_closure_of_mem hz)

