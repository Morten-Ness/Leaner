import Mathlib

variable {α : Type*} [LinearOrderedCommGroupWithZero α]

theorem WithZero.withZeroUnitsEquiv_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)) := by
  intro a b
  cases a <;> cases b <;>
  simp

