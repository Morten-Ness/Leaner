import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

variable (f : ∀ i, M i →+ N i)

theorem mker_map :
    AddMonoidHom.mker (map f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mker (f i))).comap (coeFnAddMonoidHom M) := DFinsupp.mker_mapRangeAddMonoidHom f

