import Mathlib

variable {k G : Type*}

variable [One G] [AddMonoidWithOne k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem toFinsupp_eq_single_one_one_iff {a : SkewMonoidAlgebra k G} :
    a.toFinsupp = Finsupp.single 1 1 ↔ a = 1 := by
  simp [← SkewMonoidAlgebra.toFinsupp_inj]

