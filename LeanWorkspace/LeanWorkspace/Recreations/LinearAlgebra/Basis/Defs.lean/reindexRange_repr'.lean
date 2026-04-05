import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

theorem reindexRange_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
    b.reindexRange.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i := by
  nontriviality
  subst h
  apply (Module.Basis.repr_apply_eq b (fun x i => b.reindexRange.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp only [Pi.smul_apply, map_smul, Finsupp.coe_smul]
  · intro i
    ext j
    simp only [Module.Basis.reindexRange_repr_self]
    apply Finsupp.single_apply_left (f := fun i => (⟨b i, _⟩ : Set.range b))
    exact fun i j h => Module.Basis.injective b (Subtype.mk.inj h)

