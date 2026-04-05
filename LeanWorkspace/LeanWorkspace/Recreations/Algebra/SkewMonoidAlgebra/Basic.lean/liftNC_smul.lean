import Mathlib

variable {k G : Type*}

variable [Semiring k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem liftNC_smul [MulOneClass G] {R : Type*} [Semiring R] (f : k →+* R) (g : G →* R) (c : k)
    (φ : SkewMonoidAlgebra k G) :
    SkewMonoidAlgebra.liftNC (f : k →+ R) g (c • φ) = f c * SkewMonoidAlgebra.liftNC (f : k →+ R) g φ := by
  suffices this :
    (SkewMonoidAlgebra.liftNC ↑f g).comp (smulAddHom k (SkewMonoidAlgebra k G) c) =
      (AddMonoidHom.mulLeft (f c)).comp (SkewMonoidAlgebra.liftNC ↑f g) by simpa using congr($this φ)
  refine SkewMonoidAlgebra.addHom_ext' fun a => AddMonoidHom.ext fun b => ?_
  simp [SkewMonoidAlgebra.smul_single, mul_assoc]

