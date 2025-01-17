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

Definition map_double (ls : list Z) :=
  list_rect
    _
    nil
    (fun x xs rec
     => dlet y := x + x in
         y :: rec)
    ls.

Definition make (n : nat) (m : nat) (v : Z)
  := nat_rect
       _
       (List.repeat v n)
       (fun _ rec => map_double rec)
       m.

Module Type AxT.
  Axiom Let_InAx : forall {A P} (x : A) (f : forall a : A, P a), P x.
  Axiom ZAddAx : Z -> Z -> Z.
End AxT.
Module Import Ax : AxT.
  Definition Let_InAx : forall {A P} (x : A) (f : forall a : A, P a), P x
    := @Let_In.
  Definition ZAddAx : Z -> Z -> Z
    := Z.add.
End Ax.

Definition map_double_cps {T} (ls : list Z) (k : list Z -> T) :=
  list_rect
    (fun _ => (list Z -> T) -> _)
    (fun k => k nil)
    (fun x xs rec k
     => Let_InAx (ZAddAx x x)
                 (fun y =>
                    rec (fun ys => k (y :: ys))))
    ls
    k.

Definition make_cps {T} (n : nat) (m : nat) (v : Z) (k : list Z -> T)
  := nat_rect
       _
       (fun k => k (List.repeat v n))
       (fun _ rec k => rec (fun ls => map_double_cps ls k))
       m
       k.

Lemma lift_let_list_rect T A P N C (v : A) fls
  : @list_rect T P N C (Let_In v fls) = Let_In v (fun v => @list_rect T P N C (fls v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_let_list_rect : mydb2.
Lemma lift_let_cons T A x (v : A) f : @cons T x (Let_In v f) = Let_In v (fun v => @cons T x (f v)).
Proof. reflexivity. Qed.
Hint Rewrite lift_let_cons : mydb1.

Notation goal n m := (forall v, make n m v = nil) (only parsing).
Notation goal_cps n m := (forall v, make_cps n m v (fun x => x) = nil) (only parsing).
Ltac start _ := cbv [make map_double make_cps map_double_cps]; intros.
Ltac verify_form term :=
  lazymatch term with
  | ?Let_In_f (?Add ?v ?v) (fun x => ?rest)
    => is_var v;
       lazymatch Let_In_f with
       | @Let_In _ _ => idtac
       | @Let_InAx _ _ => idtac
       | _ => fail 0 "invalid let_in" Let_In_f
       end;
       lazymatch Add with
       | Z.add => idtac
       | ZAddAx => idtac
       | _ => fail 0 "invalid add" Add
       end;
       let x' := fresh in
       let __ := constr:(fun x' : Z
                         => ltac:(let rest' := constr:(match x' return _ with x => rest end) in
                                  verify_form rest';
                                  exact I)) in
       idtac
  | cons ?v ?rest => is_var v; verify_form rest
  | nil => idtac
  | _ => fail 0 "invalid:" term
  end.
Ltac verify _ :=
  lazymatch goal with
  | [ |- ?lhs = nil ]
    => verify_form lhs
  end.

Inductive red_kind := vm | native | cbv | lazy | cbn | simpl.
Inductive rewrite_strat_kind := topdown_bottomup | bottomup_bottomup.
Inductive kind_of_rewrite := kind_rewrite_strat (_ : rewrite_strat_kind) | kind_setoid_rewrite | kind_red (_ : red_kind).

Local Notation "'eta_kind' ( k' => f ) k"
  := match k with
     | kind_rewrite_strat topdown_bottomup
       => subst! (kind_rewrite_strat topdown_bottomup) for k' in f
     | kind_rewrite_strat bottomup_bottomup
       => subst! (kind_rewrite_strat bottomup_bottomup) for k' in f
     | kind_setoid_rewrite => subst! kind_setoid_rewrite for k' in f
     | kind_red vm => subst! (kind_red vm) for k' in f
     | kind_red native => subst! (kind_red native) for k' in f
     | kind_red cbv => subst! (kind_red cbv) for k' in f
     | kind_red lazy => subst! (kind_red lazy) for k' in f
     | kind_red cbn => subst! (kind_red cbn) for k' in f
     | kind_red simpl => subst! (kind_red simpl) for k' in f
     end
       (only parsing, at level 70, k' ident).

Local Lemma sanity : forall T f k, eta_kind (k => f k) k = f k :> T.
Proof. intros; repeat match goal with |- context[match ?e with _ => _ end] => destruct e end; reflexivity. Qed.

Definition size_of_arg (arg : Z * Z) : Z
  := fst arg * snd arg.

Definition invert_size_of_arg_dumb (v : Z) : Z * Z
  := (1%Z, v).

Local Lemma invert_size_of_arg_dumb_correct v
  : size_of_arg (invert_size_of_arg_dumb v) = v.
Proof. cbv [size_of_arg invert_size_of_arg_dumb]; cbn [fst snd]; lia. Qed.

Local Instance Z_prod_has_compress : Sample.has_compress (Z * Z) Z := size_of_arg.
Local Instance Z_prod_has_make : Sample.has_make (Z * Z) Z := { make_T := invert_size_of_arg_dumb ; make_T_correct := invert_size_of_arg_dumb_correct }.

(*
           := match test_tac_n, s with
              | 0, SuperFast => (10, 10)
              | 3, SuperFast => (50, 50)
              | 4, SuperFast => (50, 50)
              | _, SuperFast => (5, 4)
              | 0, Fast => (90, 90)
              | 3, Fast => (150, 150) (* N.B. test 3 stack overflows on larger than ~160, 160 *)
              | 4, Fast => (150, 150)
              | _, Fast => (6, 5)
              | 0, Medium => (115, 115) (* maybe should be (150, 150), but (115, 115) already takes over 11 h, I think *)
              | 5, Medium => (7, 8)
              | _, Medium => (6, 7)
              | 0, Slow => (200, 200) (* ??? *)
              | _, Slow => (10, 10) (* ??? *)
              | 0, VerySlow => (400, 400) (* ??? *)
              | _, VerySlow => (100, 100) (* ??? *)
              end in*)

Definition size_of_kind (k : kind_of_rewrite) (arg : Z * Z) : Q
  := let termsize := size_of_arg arg in
     let x := inject_Z termsize in
     (* N.B. vm,cbv,lazy,native are expressions for all the data; the others are for when n=1, and are upper bounds in other cases *)
     match k with
     | kind_rewrite_strat bottomup_bottomup
       => 0.0144 * Sample.Qexp (0.415 * x)
     | kind_rewrite_strat topdown_bottomup
       => 0.0176 * Sample.Qexp (0.407 * x)
     | kind_setoid_rewrite
       => -9.89E-03 + 0.0529*x + -0.016*x^2 + 2.61E-03*x^3
     | kind_red vm
       => 5.19E-05 + 5.01E-06*x + 3.5E-10*x^2
     | kind_red native
       => 0.0685 + 1.09E-05*x + 1.71E-10*x^2
     | kind_red cbv
       => -6.28E-04 + 3.01E-06*x + 1.23E-10*x^2
     | kind_red lazy
       => -2.68E-03 + 4.72E-06*x + 1.39E-10*x^2
     | kind_red cbn
       => 0.0183 + 6.42E-04*x + 8.04E-06*x^2
     | kind_red simpl
       => -0.0116 + 2.8E-04*x + 2.28E-06*x^2
     end%Q.

Definition max_input_of_kind (k : kind_of_rewrite) : option (Z * Z)
  := match k with
     | kind_rewrite_strat _
       => None
     | kind_setoid_rewrite
       => None
     | kind_red vm
       => Some (110, 110) (* stack overflows on things much larger than this *)
     | kind_red native
       => Some (110, 110) (* stack overflows on (20880, 1) *)
     | kind_red cbv
       => Some (140, 140) (* stack overflows on (25760, 1) *)
     | kind_red lazy
       => Some (140, 140) (* stack overflows on (22052, 1) *)
     | kind_red cbn
       => None
     | kind_red simpl
       => None
     end%Z.

Local Hint Unfold size_of_kind size_of_arg : solve_factors_through_prod.
Local Existing Instance Sample.Z_prod_has_alloc.

Definition args_of_size' (k : kind_of_rewrite) (s : size) : list (Z * Z)
  := Eval cbv beta iota in
      eta_size
        (s'
         => if match s' with Sanity => true | _ => false end
            then [(1, 1); (1, 2); (2, 1); (1, 3); (3, 1); (2, 2); (4, 1); (1, 4)]
            else eta_kind
                   (k'
                    => Sample.generate_inputs
                         (T:=Z*Z)
                         (1, 1)
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


Ltac mkgoal kind nm
  := let Z_to_nat := (eval cbv in Z.to_nat) in
     lazymatch nm with
     | (?n, ?m)
       => let n := constr:(id Z_to_nat n) in
          let m := constr:(id Z_to_nat m) in
          lazymatch kind with
          | kind_red _ => constr:(goal_cps n m)
          | _ => constr:(goal n m)
          end
     end.
Ltac redgoal _ := start ().
Ltac describe_goal nm :=
  lazymatch nm with
  | (?n, ?m)
    => let sz := (eval cbv in (size_of_arg nm)) in
       idtac "Params: 0-nm=" sz ", 1-n=" n ", 2-m=" m
  end.

Ltac time_solve_goal kind
  := lazymatch kind with
     | kind_rewrite_strat topdown_bottomup
       => fun nm
          => time "rewrite_strat(topdown,bottomup)-regression-exponential"
                  ((cbv [nat_rect List.repeat id]);
                   repeat (cbn [list_rect];
                           (rewrite_strat ((try repeat topdown hints mydb1); (try repeat bottomup hints mydb2)))))
     | kind_rewrite_strat bottomup_bottomup
       => fun nm
          => time "rewrite_strat(bottomup,bottomup)-regression-exponential"
                  ((cbv [nat_rect List.repeat id]);
                   repeat (cbn [list_rect];
                           (rewrite_strat ((try repeat bottomup hints mydb1); (try repeat bottomup hints mydb2)))))
     | kind_setoid_rewrite
       => fun nm
          => time "setoid_rewrite-regression-cubic"
                  (cbv [nat_rect List.repeat id];
                   repeat (cbn [list_rect];
                           repeat setoid_rewrite lift_let_cons;
                           repeat setoid_rewrite lift_let_list_rect))
     | kind_red vm
       => fun nm
          => time "cps+vm_compute-regression-quadratic" vm_compute
     | kind_red native
       => fun nm
          => time "cps+native_compute-regression-quadratic" native_compute
     | kind_red cbv
       => fun nm
          => time "cps+cbv-regression-quadratic" cbv
     | kind_red lazy
       => fun nm
          => time "cps+lazy-regression-quadratic" lazy
     | kind_red cbn
       => fun nm
          => time "cps+cbn-regression-quadratic" (cbv delta [id]; cbn)
     | kind_red simpl
       => fun nm
          => time "cps+simpl-regression-quadratic" (cbv delta [id]; simpl)
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

for i, c in enumerate(('kind_rewrite_strat topdown_bottomup', 'kind_rewrite_strat bottomup_bottomup', 'kind_setoid_rewrite', 'kind_red vm', 'kind_red native', 'kind_red cbv', 'kind_red lazy', 'kind_red cbn', 'kind_red simpl')):
    print(f'Ltac mkgoal{i} := mkgoal constr:({c}).\nLtac time_solve_goal{i} := time_solve_goal constr:({c}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size ({c})) describe_goal mkgoal{i} redgoal time_solve_goal{i} verify sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:(kind_rewrite_strat topdown_bottomup).
Ltac time_solve_goal0 := time_solve_goal constr:(kind_rewrite_strat topdown_bottomup).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite_strat topdown_bottomup)) describe_goal mkgoal0 redgoal time_solve_goal0 verify sz.

Ltac mkgoal1 := mkgoal constr:(kind_rewrite_strat bottomup_bottomup).
Ltac time_solve_goal1 := time_solve_goal constr:(kind_rewrite_strat bottomup_bottomup).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size (kind_rewrite_strat bottomup_bottomup)) describe_goal mkgoal1 redgoal time_solve_goal1 verify sz.

Ltac mkgoal2 := mkgoal constr:(kind_setoid_rewrite).
Ltac time_solve_goal2 := time_solve_goal constr:(kind_setoid_rewrite).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size (kind_setoid_rewrite)) describe_goal mkgoal2 redgoal time_solve_goal2 verify sz.

Ltac mkgoal3 := mkgoal constr:(kind_red vm).
Ltac time_solve_goal3 := time_solve_goal constr:(kind_red vm).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size (kind_red vm)) describe_goal mkgoal3 redgoal time_solve_goal3 verify sz.

Ltac mkgoal4 := mkgoal constr:(kind_red native).
Ltac time_solve_goal4 := time_solve_goal constr:(kind_red native).
Ltac run4 sz := Harness.runtests_verify_sanity (args_of_size (kind_red native)) describe_goal mkgoal4 redgoal time_solve_goal4 verify sz.

Ltac mkgoal5 := mkgoal constr:(kind_red cbv).
Ltac time_solve_goal5 := time_solve_goal constr:(kind_red cbv).
Ltac run5 sz := Harness.runtests_verify_sanity (args_of_size (kind_red cbv)) describe_goal mkgoal5 redgoal time_solve_goal5 verify sz.

Ltac mkgoal6 := mkgoal constr:(kind_red lazy).
Ltac time_solve_goal6 := time_solve_goal constr:(kind_red lazy).
Ltac run6 sz := Harness.runtests_verify_sanity (args_of_size (kind_red lazy)) describe_goal mkgoal6 redgoal time_solve_goal6 verify sz.

Ltac mkgoal7 := mkgoal constr:(kind_red cbn).
Ltac time_solve_goal7 := time_solve_goal constr:(kind_red cbn).
Ltac run7 sz := Harness.runtests_verify_sanity (args_of_size (kind_red cbn)) describe_goal mkgoal7 redgoal time_solve_goal7 verify sz.

Ltac mkgoal8 := mkgoal constr:(kind_red simpl).
Ltac time_solve_goal8 := time_solve_goal constr:(kind_red simpl).
Ltac run8 sz := Harness.runtests_verify_sanity (args_of_size (kind_red simpl)) describe_goal mkgoal8 redgoal time_solve_goal8 verify sz.

Global Hint Opaque Let_In : rewrite typeclass_instances.
Global Opaque Let_In.
Global Instance : forall {A}, Proper (eq ==> eq ==> Basics.flip Basics.impl) (@eq A) := _.
Global Instance : Proper (eq ==> eq)
                         (list_rect (fun _ : list Z => list Z) []
                                    (fun (x : Z) (_ rec : list Z) =>
                                       dlet y : Z := x + x in
                                         y :: rec))
  := _.
Global Instance : forall {A B x}, Proper (pointwise_relation _ eq ==> eq) (@Let_In A (fun _ => B) x)
  := _.
Global Instance : forall {A B x}, Proper (forall_relation (fun _ => eq) ==> eq) (@Let_In A (fun _ => B) x)
  := _.
Global Instance : forall {A}, ProperProxy eq (@nil A) := _.
Global Instance : forall A x, Proper (eq ==> eq) (@cons A x) := _.
Global Instance : Transitive (Basics.flip Basics.impl) := _.

Global Set NativeCompute Timing.
Global Open Scope Z_scope.
(*
Goal True.

  run8 SuperFast.
  let v := mkgoal7 (3, 3) in
  assert v; [ redgoal () | ].
  time_solve_goal7 ().
  verify ().
  cbn [list_rect].

  Typeclasses eauto := debug.
  cbn [nat_rect].
  setoid_rewrite lift_let_list_rect.
  try setoid_rewrite lift_let_cons.

  rewrite_strat
  repeat (cbn [nat_rect]; rewrite_strat ((try repeat topdown hints mydb1); (try repeat bottomup hints mydb2))).
*)
