import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem coplanar_iff_finrank_le_two {s : Set P} [FiniteDimensional k (vectorSpan k s)] :
    Coplanar k s ↔ finrank k (vectorSpan k s) ≤ 2 := by
  have h : Coplanar k s ↔ Module.rank k (vectorSpan k s) ≤ 2 := Iff.rfl
  rw [← finrank_eq_rank] at h
  exact mod_cast h

alias ⟨Coplanar.finrank_le_two, _⟩ := coplanar_iff_finrank_le_two

