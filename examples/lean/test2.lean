-- test.lean
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n ih => rw [Nat.succ_add, Nat.add_succ, ih]
