import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem Coplanar.finiteDimensional_vectorSpan {s : Set P} (h : Coplanar k s) :
    FiniteDimensional k (vectorSpan k s) := by
  refine IsNoetherian.iff_fg.1 (IsNoetherian.iff_rank_lt_aleph0.2 (lt_of_le_of_lt h ?_))
  exact Cardinal.lt_aleph0.2 ⟨2, rfl⟩

