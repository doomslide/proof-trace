import Mathlib.Data.Nat.Basic

theorem add_assoc_example (a b c : Nat) : a + b + c = a + (b + c) := by
  rw [Nat.add_assoc]
