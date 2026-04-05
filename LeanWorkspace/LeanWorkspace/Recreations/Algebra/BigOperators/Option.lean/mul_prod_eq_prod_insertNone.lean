import Mathlib

variable {α M : Type*} [CommMonoid M]

theorem mul_prod_eq_prod_insertNone (f : α → M) (x : M) (s : Finset α) :
    x * ∏ i ∈ s, f i = ∏ i ∈ insertNone s, i.elim x f := (Finset.prod_insertNone (fun i => i.elim x f) _).symm

