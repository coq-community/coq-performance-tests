Declare ML Module "sandbox".

Ltac sandbox tac :=
  catch_success (once tac (); raise_success).

Tactic Notation "sandbox" tactic3(tac) := sandbox ltac:(fun _ => tac).
