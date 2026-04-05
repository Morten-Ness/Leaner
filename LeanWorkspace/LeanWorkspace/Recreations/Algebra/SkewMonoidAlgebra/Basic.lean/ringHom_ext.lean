import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Monoid G] [MulSemiringAction G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem ringHom_ext {f g : SkewMonoidAlgebra k G →+* k} (h₁ : ∀ b, f (SkewMonoidAlgebra.single 1 b) = g (SkewMonoidAlgebra.single 1 b))
    (h_of : ∀ a, f (SkewMonoidAlgebra.single a 1) = g (SkewMonoidAlgebra.single a 1)) : f = g := have {a : G} {b₁ b₂ : k} : (SkewMonoidAlgebra.single 1 b₁) * (SkewMonoidAlgebra.single a b₂) = SkewMonoidAlgebra.single a (b₁ * b₂) := by
    simp [SkewMonoidAlgebra.single_mul_single, one_mul, one_smul]
  RingHom.coe_addMonoidHom_injective <|
    SkewMonoidAlgebra.addHom_ext fun a b ↦ by rw [← mul_one b, ← this, AddMonoidHom.coe_coe f,
      AddMonoidHom.coe_coe g, f.map_mul, g.map_mul, h₁, h_of]

