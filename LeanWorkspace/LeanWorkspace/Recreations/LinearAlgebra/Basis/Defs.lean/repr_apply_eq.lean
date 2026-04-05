import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}

variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable (b : Basis ι R M)

variable {R₁ : Type*} [Semiring R₁] {σ : R →+* R₁} {σ' : R₁ →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

variable {M₁ : Type*} [AddCommMonoid M₁] [Module R₁ M₁]

theorem repr_apply_eq (f : M → ι → R) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x) (f_eq : ∀ i, f (b i) = Finsupp.single i 1)
    (x : M) (i : ι) : b.repr x i = f x i := by
  let f_i : M →ₗ[R] R :=
    { toFun x := f x i
      map_add' _ _ := by rw [hadd, Pi.add_apply]
      map_smul' _ _ := by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine Module.Basis.ext b fun j => ?_
    change b.repr (b j) i = f (b j) i
    rw [Module.Basis.repr_self b, f_eq]
  calc
    b.repr x i = f_i x := by
      { rw [← this]
        rfl }
    _ = f x i := rfl

