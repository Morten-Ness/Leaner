import Mathlib

theorem toAdd_pow (a : Multiplicative ℤ) (b : ℕ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

