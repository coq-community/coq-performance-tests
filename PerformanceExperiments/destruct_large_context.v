Require Import PerformanceExperiments.Harness.
Fixpoint mkgoal_nat (n : nat) : Prop
  := match n with
     | O => True /\ True -> True
     | S n => Z.div_eucl = Z.div_eucl -> mkgoal_nat n
     end.

Global Set Warnings Append "-abstract-large-number".

Ltac mkgoal n := constr:(mkgoal_nat (Z.to_nat n)).
Ltac redgoal _ := idtac.
Ltac step_goal _ :=
  let __ := match goal with
            | _ => (let H := fresh in
                    pose proof (eq_refl Z.div_eucl) as H;
                    lazy in H)
            end in
  constr:(True).

Ltac time_solve_goal0 n :=
  idtac;
  time "lazy-regression-linear" lazy;
  time "intros-regression-linear" intros;
  let H := fresh in
  assert_succeeds (pose proof (conj I I) as H;
                   assert_succeeds (time "destruct-and-regression-linear" destruct H);
                   assert_succeeds (time "case-clear-intros-and-regression-linear" (time "case-and-regression-linear" case H; clear H; intros)));
  assert_succeeds (pose proof (@or_introl True True I) as H;
                   assert_succeeds (time "destruct-or-regression-linear" destruct H);
                   assert_succeeds (time "case-clear-intros-or-regression-linear" (time "case-or-regression-linear" case H; clear H; intros))).

Global Open Scope Z_scope.

Definition args_of_size (s : size) : list Z
  := match s with
     | Sanity => List.map Z.of_nat (seq 1 3)
     | SuperFast => List.map Z.of_nat (seq 1 10)
     | Fast => List.map (fun x => Z.of_nat x * 50) (seq 1 4)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz(*Harness.runtests_step args_of_size default_describe_goal step_goal redgoal time_solve_goal0 sz*).
(*
Goal True. run0 Sanity. run0 SuperFast. run0 Fast. Abort.
*)
