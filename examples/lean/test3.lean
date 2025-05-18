import Lean

/-- Simple theorem with a non-trivial proof -/
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ n IH =>
    rw [Nat.succ_add]
    rw [Nat.add_succ]
    rw [IH]
