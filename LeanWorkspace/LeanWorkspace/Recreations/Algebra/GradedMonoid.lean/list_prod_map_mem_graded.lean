import Mathlib

variable {ι : Type*}

variable {R : Type*}

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

theorem list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' → ι) (r : ι' → R)
    (h : ∀ j ∈ l, r j ∈ A (i j)) : (l.map r).prod ∈ A (l.map i).sum := by
  match l with
  | [] =>
    rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil]
    exact one_mem_graded _
  | head::tail =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact
      mul_mem_graded (h _ List.mem_cons_self)
        (list_prod_map_mem_graded tail _ _ fun j hj => h _ <| List.mem_cons_of_mem _ hj)

