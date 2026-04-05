import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem Splits.listProd {l : List R[X]} (h : ∀ f ∈ l, Polynomial.Splits f) : Polynomial.Splits l.prod := list_prod_mem h

