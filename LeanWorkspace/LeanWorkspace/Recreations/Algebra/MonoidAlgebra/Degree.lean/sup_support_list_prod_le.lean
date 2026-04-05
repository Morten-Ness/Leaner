import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [Semiring R]

variable [AddMonoid A] [AddMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

theorem sup_support_list_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) :
    ∀ l : List R[A],
      l.prod.support.sup degb ≤ (l.map fun f : R[A] => f.support.sup degb).sum
  | [] => by
    rw [List.map_nil, Finset.sup_le_iff, List.prod_nil, List.sum_nil]
    exact fun a ha => by rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset ha)]
  | f::fs => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    grw [AddMonoidAlgebra.sup_support_mul_le degbm, sup_support_list_prod_le degb0 degbm]
