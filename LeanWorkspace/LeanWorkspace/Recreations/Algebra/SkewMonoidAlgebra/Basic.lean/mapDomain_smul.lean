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

theorem mapDomain_smul {R : Type*} [Monoid R] [DistribMulAction R k] {b : R} :
    SkewMonoidAlgebra.mapDomain f (b • v) = b • SkewMonoidAlgebra.mapDomain f v := by
  simp_rw [← SkewMonoidAlgebra.toFinsupp_inj, SkewMonoidAlgebra.toFinsupp_smul, SkewMonoidAlgebra.toFinsupp_mapDomain]
  simp [Finsupp.mapDomain_smul]

