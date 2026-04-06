import Mathlib

variable {R S V W P : Type*} [Ring R] [Ring S]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] [AddTorsor V P]
  [AddCommGroup W] [Module R W] [Module S W] [Module.Finite S W] [SMulCommClass R S W]

theorem finrank_eq [Module.Free S W] [StrongRankCondition R] [StrongRankCondition S] :
    Module.finrank S (P →ᵃ[R] W) = (Module.finrank R V + 1) * Module.finrank S W := by
  simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
    AffineMap.finrank_eq (R := R) (S := S) (V := V) (W := W) (P := P)
