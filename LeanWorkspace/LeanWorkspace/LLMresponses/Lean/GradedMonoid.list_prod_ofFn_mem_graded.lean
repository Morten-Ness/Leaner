import Mathlib

variable {ι : Type*}

variable {R : Type*}

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

theorem list_prod_ofFn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).prod ∈ A (List.ofFn i).sum := by
  classical
  induction n with
  | zero =>
      simpa using (SetLike.one_mem_graded (A := A) : (1 : R) ∈ A (0 : ι))
  | succ n ih =>
      let i' : Fin n → ι := fun j => i j.succ
      let r' : Fin n → R := fun j => r j.succ
      have h' : ∀ j, r' j ∈ A (i' j) := by
        intro j
        exact h j.succ
      have hhead : r 0 ∈ A (i 0) := h 0
      have htail : (List.ofFn r').prod ∈ A (List.ofFn i').sum := ih i' r' h'
      simpa [List.ofFn_succ, i', r', add_assoc] using SetLike.mul_mem_graded hhead htail
