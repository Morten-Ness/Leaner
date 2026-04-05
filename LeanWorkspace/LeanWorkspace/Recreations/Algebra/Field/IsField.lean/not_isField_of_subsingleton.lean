import Mathlib

theorem not_isField_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬IsField R := fun h =>
  let ⟨_, _, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)

