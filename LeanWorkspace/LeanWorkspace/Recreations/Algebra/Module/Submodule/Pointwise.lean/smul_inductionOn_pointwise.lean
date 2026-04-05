import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem smul_inductionOn_pointwise [SMulCommClass S R M] {a : S} {p : (x : M) → x ∈ a • N → Prop}
    (smul₀ : ∀ (s : M) (hs : s ∈ N), p (a • s) (Submodule.smul_mem_pointwise_smul _ _ _ hs))
    (smul₁ : ∀ (r : R) (m : M) (mem : m ∈ a • N), p m mem → p (r • m) (Submodule.smul_mem _ _ mem))
    (add : ∀ (x y : M) (hx : x ∈ a • N) (hy : y ∈ a • N),
      p x hx → p y hy → p (x + y) (Submodule.add_mem _ hx hy))
    (zero : p 0 (Submodule.zero_mem _)) {x : M} (hx : x ∈ a • N) :
    p x hx := by
  simp_all only [← Submodule.singleton_set_smul]
  let p' (x : M) (hx : x ∈ ({a} : Set S) • N) : Prop :=
    p x (by rwa [← Submodule.singleton_set_smul])
  refine Submodule.set_smul_inductionOn (motive := p') _ (N.singleton_set_smul a ▸ hx)
      (fun r n hr hn ↦ ?_) smul₁ add zero
  · push _ ∈ _ at hr
    subst hr
    exact smul₀ n hn

-- Note that this can't be generalized to `Set S`, because even though `SMulCommClass R R M` implies
-- `SMulComm R R N` for all `R`-submodules `N`, `SMulCommClass R S N` for all `R`-submodules `N`
-- does not make sense. If we just focus on `R`-submodules that are also `S`-submodule, then this
-- should be true.

