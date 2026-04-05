import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable {R : Type u} {ι : Type v} {M : ι → Type w} {N : ι → Type*}

theorem ker_map [∀ i, AddCommGroup (M i)] [∀ i, AddCommMonoid (N i)] (f : ∀ i, M i →+ N i) :
    (map f).ker =
      (AddSubgroup.pi Set.univ (f · |>.ker)).comap (DirectSum.coeFnAddMonoidHom M) := DFinsupp.ker_mapRangeAddMonoidHom f

