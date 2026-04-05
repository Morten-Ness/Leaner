import Mathlib

variable {α β : Type*}

theorem nsmul_replicate {a : α} (n m : ℕ) : n • replicate m a = replicate (n * m) a := ((Multiset.replicateAddMonoidHom a).map_nsmul _ _).symm

