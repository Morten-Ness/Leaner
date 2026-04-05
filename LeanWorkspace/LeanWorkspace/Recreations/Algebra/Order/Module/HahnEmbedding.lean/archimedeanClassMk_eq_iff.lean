import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_eq_iff [IsOrderedAddMonoid R] (x y : f.val.domain) :
    ArchimedeanClass.mk (f.val x) = .mk (f.val y) ↔ ArchimedeanClass.mk x.val = .mk y.val := by
  simp_rw [← HahnEmbedding.Partial.toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans ArchimedeanClass.mk x = .mk y
  · exact Function.Injective.eq_iff <| orderHom_injective <| HahnEmbedding.Partial.toOrderAddMonoidHom_injective _
  · simp_rw [mk_eq_mk]
    aesop

