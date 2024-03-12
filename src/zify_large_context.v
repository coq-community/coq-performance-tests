(** Testing the performance of [zify] and [Z.to_euclidean_division_equations].
For not regressing on COQBUG(https://github.com/coq/coq/issues/18770) *)
From Coq Require Import ZArith List Zify.
Import ListNotations.

Global Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Ltac mkgoal n := exact (fold_left (fun T _ => (forall x, 0 <= x < 100 -> T)) (repeat tt n) False).

Goal ltac:(mkgoal 10%nat).
  simpl. intros. Time zify.
Abort.

Goal ltac:(mkgoal 100%nat).
  simpl. intros. Time zify.
Abort.

Goal ltac:(mkgoal 200%nat).
  simpl. intros. Time zify.
Abort.
