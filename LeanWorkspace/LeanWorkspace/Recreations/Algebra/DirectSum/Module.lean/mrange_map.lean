import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (f : ∀ i, M i →+ N i)

theorem mrange_map :
    AddMonoidHom.mrange (map f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mrange (f i))).comap (coeFnAddMonoidHom N) := DFinsupp.mrange_mapRangeAddMonoidHom f

