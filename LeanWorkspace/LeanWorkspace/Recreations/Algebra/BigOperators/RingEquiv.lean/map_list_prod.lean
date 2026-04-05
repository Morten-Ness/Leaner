import Mathlib

variable {α R S : Type*}

theorem map_list_prod [Semiring R] [Semiring S] (f : R ≃+* S) (l : List R) :
    f l.prod = (l.map f).prod := map_list_prod f l

