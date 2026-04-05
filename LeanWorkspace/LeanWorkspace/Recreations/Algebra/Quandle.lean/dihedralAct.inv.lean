import Mathlib

variable {Q : Type*} [Quandle Q]

theorem dihedralAct.inv (n : ℕ) (a : ZMod n) : Function.Involutive (Quandle.dihedralAct n a) := by
  intro b
  dsimp only [Quandle.dihedralAct]
  simp

