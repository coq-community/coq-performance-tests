Require Import PerformanceExperiments.Lock.

Definition locked_nat_mul := lock Nat.mul.
Definition lock_Nat_mul : Nat.mul = locked_nat_mul
  := eq_sym (unlock _).
