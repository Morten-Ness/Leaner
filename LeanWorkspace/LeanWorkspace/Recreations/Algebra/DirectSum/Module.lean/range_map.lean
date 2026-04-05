import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable {R} {N : ι → Type*}

variable {R : Type u} {ι : Type v} {M : ι → Type w} {N : ι → Type*}

theorem range_map [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] (f : ∀ i, M i →+ N i) :
    (map f).range =
      (AddSubgroup.pi Set.univ (f · |>.range)).comap (DirectSum.coeFnAddMonoidHom N) := DFinsupp.range_mapRangeAddMonoidHom f

