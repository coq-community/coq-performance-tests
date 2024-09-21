From Coq Require Import Lia.
From Coq Require Import ZArith.
From Coq Require Import QArith.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.
From Coq Require Import List.
Require Import PerformanceExperiments.Harness.
Require PerformanceExperiments.Sample.
Require Export PerformanceExperiments.LetIn PerformanceExperiments.ListRectInstances.
Import ListNotations.
Local Open Scope list_scope. Local Open Scope Z_scope.

Definition make_lets_def (n : nat) (v : Z) (acc : Z) :=
  @nat_rect
    (fun _ => Z * Z -> Z)
    (fun '(v, acc) => acc + acc + v)
    (fun _ rec '(v, acc) => dlet acc := acc + acc + v in rec (v, acc))
    n
    (v, acc).

Notation goal n := (forall acc, make_lets_def n 0 acc = acc) (only parsing).
Ltac start _ := cbv [make_lets_def]; intros.
Ltac verify_form start term :=
  lazymatch term with
  | (dlet x := start + start in ?rest)
    => let x' := fresh in
       let __ := constr:(fun x' : Z
                         => ltac:(let rest' := constr:(match x' return _ with x => rest end) in
                                  verify_form x' rest';
                                  exact I)) in
       idtac
  | start + start => idtac
  end.
Ltac verify _ :=
  lazymatch goal with
  | [ |- ?lhs = ?acc ]
    => is_var acc; verify_form acc lhs
  end.

Hint Rewrite Z.add_0_r : mydb.

Inductive rewrite_strat_kind := topdown | bottomup.
Inductive kind_of_rewrite := kind_rewrite_strat (_ : rewrite_strat_kind) | kind_setoid_rewrite.

Local Notation "'eta_kind' ( k' => f ) k"
  := match k with
     | kind_rewrite_strat topdown
       => subst! (kind_rewrite_strat topdown) for k' in f
     | kind_rewrite_strat bottomup
       => subst! (kind_rewrite_strat bottomup) for k' in f
     | kind_setoid_rewrite => subst! kind_setoid_rewrite for k' in f
     end
       (only parsing, at level 70, k' ident).

Local Lemma sanity : forall T f k, eta_kind (k => f k) k = f k :> T.
Proof. intros; repeat match goal with |- context[match ?e with _ => _ end] => destruct e end; reflexivity. Qed.

(*
    := match test_tac_n, s with
       | 0, SuperFast => [(1, 70, 1)]
       | 1, SuperFast => [(1, 70, 1)]
       | 2, SuperFast => [(1, 30, 1)]
       | 3, SuperFast => [(1, 30, 1)]
       | 0, Fast => [(71, 5000, 1)]
       | 1, Fast => [(71, 200, 1)]
       | 2, Fast => [(31, 60, 1)]
       | 3, Fast => [(31, 60, 1)]
       | 1, Medium => [(201, 371, 1)]
       | 2, Medium => [(61, 90, 1)]
       | 3, Medium => [(61, 90, 1)]
       | 1, Slow => [(372, 1000, 1)] (* ??? *)
       | 2, Slow => [(91, 600, 1)] (* ??? *)
       | 3, Slow => [(91, 600, 1)] (* ??? *)
       | 1, VerySlow => [(1001, 5000, 1)]
       | 2, VerySlow => [(601, 5000, 1)]
       | 3, VerySlow => [(601, 5000, 1)]
       | 0, _ => []
       | _, _ => []
       end.
*)

Definition size_of_kind (k : kind_of_rewrite) (arg : Z) : Q
  := let x := inject_Z arg in
     match k with
     | kind_rewrite_strat bottomup
       => -9.07 + 0.926*x + -0.0169*x^2 + 9.36E-05*x^3
     | kind_rewrite_strat topdown
       => -9.31 + 0.947*x + -0.0172*x^2 + 9.45E-05*x^3
     | kind_setoid_rewrite
       => -0.074 + 7.79E-03*x + -7.08E-05*x^2 + 1.42E-06*x^3
     end%Q.

Definition max_input_of_kind (k : kind_of_rewrite) : option Z
  := match k with
     | kind_rewrite_strat _
       => None
     | kind_setoid_rewrite
       => None
     end%Z.

Definition args_of_size' (k : kind_of_rewrite) (s : size) : list Z
  := Eval cbv beta iota in
      eta_size
        (s'
         => if match s' with Sanity => true | _ => false end
            then [0; 1; 2; 3; 4]
            else eta_kind
                   (k'
                    => Sample.generate_inputs
                         (T:=Z)
                         1
                         (size_of_kind k')
                         (Qseconds_of_size s')
                         (Qstandard_max_seconds_of_size s')
                         Sample.default_max_points
                         (max_input_of_kind k'))
                   k)
        s.
Local Set NativeCompute Profiling.
Local Set NativeCompute Timing.
(* Takes about 20 seconds *)
Time Definition args_of_size (k : kind_of_rewrite) (s : size)
  := Eval native_compute in eta_size (s' => eta_kind (k' => args_of_size' k' s') k) s.

Ltac mkgoal kind n :=
  let Z_to_nat := (eval vm_compute in Z.to_nat) in
  constr:(goal (id Z_to_nat n)).

Ltac redgoal _ := start ().
Ltac describe_goal n := idtac "Params: n=" n.

Ltac time_solve_goal kind
  := lazymatch kind with
     | kind_rewrite_strat topdown
       => fun n
          => time "rewrite_strat(topdown)-regression-exponential"
                  (cbv [nat_rect id]; repeat rewrite_strat topdown hints mydb)
     | kind_rewrite_strat bottomup
       => fun n
          => time "rewrite_strat(bottomup)-regression-exponential"
                  (cbv [nat_rect id]; repeat rewrite_strat bottomup hints mydb)
     | kind_setoid_rewrite
       => fun n
          => time "setoid_rewrite-regression-cubic"
                  (cbv [nat_rect id]; repeat setoid_rewrite Z.add_0_r)
     end.

(**
<<<

#!/usr/bin/env python3

print(r'''(**
<<<
''')
print(open(__file__, 'r').read())
print(r'''>>>
 *)''')

for i, c in enumerate(('kind_rewrite_strat topdown', 'kind_rewrite_strat bottomup', 'kind_setoid_rewrite')):
    print(f'Ltac mkgoal{i} := mkgoal constr:({c}).\nLtac time_solve_goal{i} := time_solve_goal constr:({c}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size ({c})) describe_goal mkgoal{i} redgoal time_solve_goal{i} verify sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:(kind_rewrite_strat topdown).
Ltac time_solve_goal0 := time_solve_goal constr:(kind_rewrite_strat topdown).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite_strat topdown)) describe_goal mkgoal0 redgoal time_solve_goal0 verify sz.

Ltac mkgoal1 := mkgoal constr:(kind_rewrite_strat bottomup).
Ltac time_solve_goal1 := time_solve_goal constr:(kind_rewrite_strat bottomup).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite_strat bottomup)) describe_goal mkgoal1 redgoal time_solve_goal1 verify sz.

Ltac mkgoal2 := mkgoal constr:(kind_setoid_rewrite).
Ltac time_solve_goal2 := time_solve_goal constr:(kind_setoid_rewrite).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size (kind_setoid_rewrite)) describe_goal mkgoal2 redgoal time_solve_goal2 verify sz.


Global Hint Opaque Let_In Z.add : rewrite typeclass_instances.
Global Opaque Let_In Z.add.

Global Instance : forall {A}, Proper (eq ==> eq ==> Basics.flip Basics.impl) (@eq A) := _.
Global Instance : forall {A B x}, Proper (pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => B) x)
  := _.
Global Instance : forall {A B x}, Proper (forall_relation (fun _ => eq) ==> eq) (@Let_In A (fun _ => B) x)
  := _.
Global Instance : forall {acc}, @ProperProxy Z (@eq Z) acc := _.

Global Open Scope Z_scope.
(*

Goal True.
  run2 Sanity.
*)
