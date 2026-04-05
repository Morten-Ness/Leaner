import Mathlib

variable {k G : Type*}

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem liftNC_one {g_hom R : Type*} [NonAssocSemiring k] [One G] [Semiring R] [FunLike g_hom G R]
    [OneHomClass g_hom G R] (f : k →+* R) (g : g_hom) : SkewMonoidAlgebra.liftNC (f : k →+ R) g 1 = 1 := by
  simp only [SkewMonoidAlgebra.one_def, liftNC_single, AddMonoidHom.coe_coe, map_one, mul_one]

