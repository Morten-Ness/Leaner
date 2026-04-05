import Mathlib

variable {k G : Type*}

variable [AddCommMonoid k]

variable {G' G'' : Type*} (f : G → G') {g : G' → G''} (v : SkewMonoidAlgebra k G)

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem toFinsupp_mapDomain :
    (SkewMonoidAlgebra.mapDomain f v).toFinsupp = Finsupp.mapDomain f v.toFinsupp := by
  simp_rw [mapDomain_apply, Finsupp.mapDomain, SkewMonoidAlgebra.toFinsupp_sum', SkewMonoidAlgebra.single]

