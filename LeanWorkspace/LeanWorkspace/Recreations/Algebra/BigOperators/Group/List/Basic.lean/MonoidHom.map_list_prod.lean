import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N]

theorem map_list_prod (f : M →* N) (l : List M) : f l.prod = (l.map f).prod := map_list_prod f l

