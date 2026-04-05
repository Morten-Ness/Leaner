import Mathlib

theorem FreeMagma.length_pos {α : Type u} (x : FreeMagma α) : 0 < x.length := match x with
  | FreeMagma.of _ => Nat.succ_pos 0
  | mul y z => Nat.add_pos_left (length_pos y) z.length

