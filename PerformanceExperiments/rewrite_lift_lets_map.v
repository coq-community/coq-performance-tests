Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
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

Local Notation "'subst!' x 'for' y 'in' f"
  := (match x return _ with y => f end) (only parsing, at level 30, y ident).
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

Local Existing Instance Sample.Z_prod_has_double_avg.

Definition size_of_arg (arg : Z * Z) : Z
  := fst arg * snd arg.

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
     match k with
     | kind_rewrite_strat _
       => x / 30 * 10
     | kind_setoid_rewrite
       => x / 30 * 10
     | kind_red vm
       => x / (150 * 150) * 10
     | kind_red native
       => x / (150 * 150) * 10
     | kind_red cbv
       => x / (150 * 150) * 10
     | kind_red lazy
       => x / (150 * 150) * 10
     | kind_red cbn
       => x / (150 * 150) * 10
     | kind_red simpl
       => x / (150 * 150) * 10
     end%Q.

Local Hint Unfold size_of_kind size_of_arg : solve_factors_through_prod.

Definition args_of_size (k : kind_of_rewrite) (s : size) : list (Z * Z)
  := if match s with Sanity => true | _ => false end
     then [(1, 1); (1, 2); (2, 1); (1, 3); (3, 1); (2, 2); (4, 1); (1, 4)]
     else eta_kind
            (k'
             => Sample.generate_inputs
                  (T:=Z*Z)
                  (1, 1)
                  (size_of_kind k')
                  (Qseconds_of_size s)
                  Qstandard_max_seconds)
            k.

Goal True.
  pose (args_of_size (kind_red vm) SuperFast) as x.
  cbv [args_of_size] in x.
  cbv [Qseconds_of_size Qstandard_max_seconds size_of_kind] in x.
  cbv [Zseconds_of_size inject_Z] in x.
  cbv [Zstandard_max_seconds seconds_of_size] in x.
  cbn -[Sample.generate_inputs] in x.
  cbv [Sample.generate_inputs] in x.
  set (k := Sample.find_max _ _ _ _ _) in (value of x).
  vm_compute in k.
  subst k.
  cbv [Sample.cutoff_elem_count] in x.
  cbv [Sample.binary_alloc] in x.
  set (k:= Sample.count_elems_T _ _) in (value of x) at 1; vm_compute in k; subst k.
  set (k:=(100 + _)%nat) in (value of x); vm_compute in k; subst k.
  set (fuel := 117%nat) in (value of x).
  cbn [Sample.binary_alloc_QT_fueled] in x.
  set (k := Sample.count_elems_T _ _) in (value of x) at 1; vm_compute in k; subst k.
  set (k := Sample.total_time_all_elems_T _ _) in (value of x) at 1.
  Time vm_compute in k.
  subst k.
  set (k := (_ =? _)%N) in (value of x) at 1.
  vm_compute in k; subst k.
  cbv beta iota zeta in x.
  set (k := (_ =? _)%N) in (value of x) at 1.
  vm_compute in k; subst k.
  cbv beta iota zeta in x.
  set (k := (_ <=? _)%N) in (value of x) at 1.
  vm_compute in k.
  vm_compute in k; subst k.
  cbv beta iota zeta in x.
  vm_compute orb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  pose 116%nat as fuel'.
  change fuel with (S fuel') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  vm_compute orb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Sample.avg_T in x.
  pose 115%nat as fuel''.
  change fuel' with (S fuel'') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Z.to_N in x.
  set (k := (_ / _)%Q) in (value of x) at 1; vm_compute in k; subst k.
  change fuel' with (S fuel'') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Z.to_N in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  change fuel with (S fuel') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  vm_compute orb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Sample.avg_T in x.
  change fuel' with (S fuel'') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Z.to_N in x.
  vm_compute orb in x.
  cbv beta iota zeta in x.
  vm_compute Sample.avg_T in x.
  pose 114%nat as fuel'''.
  change fuel'' with (S fuel''') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Z.to_N in x.
  set (k := (_ / _)%Q) in (value of x) at 1; vm_compute in k; subst k.
  change fuel'' with (S fuel''') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Z.to_N in x.
  set (k := (_ / _)%Q) in (value of x) at 1; vm_compute in k; subst k.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  change fuel' with (S fuel'') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k.
  vm_compute Z.to_N in x.
  vm_compute orb in x.
  cbv beta iota zeta in x.
  vm_compute Sample.avg_T in x.
  change fuel'' with (S fuel''') in (value of x) at 1.
  cbn [Sample.binary_alloc_QT_fueled] in x.
  vm_compute N.eqb in x.
  cbv beta iota zeta in x.
  vm_compute N.leb in x.
  cbv beta iota zeta in x.
  vm_compute orb in x.
  cbv beta iota zeta in x.
  repeat (set (k := Qred _) in (value of x) at 1; vm_compute in k; subst k).
  vm_compute Sample.avg_T in x.
  (** HERE TODO: set a maximum number of points to sample *)

  vm_compute Sample.binary_alloc_QT_fueled in x.
  vm_compute in x.


  set (k := (_ / _)%Q) in (value of x) at 1; vm_compute in k; subst k.
  set (k := (_ + _)%Q) in (value of x) at 1; vm_compute in k; subst k.

  vm_compute Sample.total_time_all_elems_T in x.
  vm_compute Sample.avg_T in x.
  vm_compute Qred in x.
  vm_compute in x.
  change fuel
  vm_compute in x.
  set k
  set (k := (_ - _)%Q) in (value of x) at 1; vm_compute in k; subst k.
  set (k := (_ - _)%Q) in (value of x) at 1; vm_compute in k; subst k.
  cbv [Sample.total_time_all_elems_T] in k.
  cbv [Sample.total_time_of_Z_prod_poly] in k.
  cbn [Z.to_N] in k.
  cbv [Sample.total_time_of_N_prod_poly] in k.
  cbn [fst snd] in k.
  vm_compute Sample.degree in k.
  vm_compute Nat.max in k.
  vm_compute Sample.taylor_series_ln1px in k.
  vm_compute Sample.compose_poly in k.
  vm_compute Sample.poly_mul in k.
  vm_compute Sample.integrate_poly in k.
  cbv beta iota zeta in k.
  vm_compute N.leb in k.
  cbv beta iota zeta in k.
  vm_compute Qeq_bool in k.
  set (c := Qeq_bool _ _) in (value of k); vm_compute in c; subst c.
  cbv beta iota zeta in k.
  cbv [Sample.eval_poly] in k.
  cbv [Sample.eval_poly_gen] in k.
  cbn [map] in k.
  cbn [fold_right] in k.
  vm_compute inject_Z in k.
  vm_compute Qpower in k.
  vm_compute Sample.Qln in k.
  cbv [size_of_arg] in k.
  cbn [fst snd] in k.
  pose (Qred k) as k'.
  Time vm_compute in k'.
  Time vm_compute in k'.
  Time native_compute in k'.
  Time native_compute in k'.
  pose
  Time
  Time vm_compute in k.
  native_compute in k.
  vm_compute in k.
  vm_compute Sample.poly_mul in k.
  Time vm_compute in k.
  vm_compute in k.
  vm_compute in x.
  cbv [Sample.binary_alloc_QT_fueled] in x.
  cbv [Sample.count_elems_T] in k.
  vm_compu
  clear x.
  cbv [Sample.Z_prod_has_count] in k.
  cbv [Sample.Zsum_from_to] in k.
  cbn [fst snd] in k.
  vm_compute in k.
  set (v := Z.mul _ _) in (value of k) at 1; vm_compute in v; subst v.
  set (v := Z.mul _ _) in (value of k) at 1; vm_compute in v; subst v.
  set (v := Z.mul _ _) in (value of k) at 1; vm_compute in v; subst v.
  cbv [Sample.op_from_to] in k.
  cbn [inject_Z] in k.
  vm_compute in k.
  cbv [Sample.alloc_T Sample.total_time_all_elems_T Sample.count_elems_T] in x.
  cbv [Sample.Z_prod_has_alloc
  set (k :=
  cbv [Sample.sort_by_size_and_alloc]

Ltac mkgoal kind nm
  := lazymatch nm with
     | (?n, ?m)
       => let n := (eval vm_compute in (Z.to_nat n)) in
          let m := (eval vm_compute in (Z.to_nat m)) in
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
          => time "rewrite_strat(topdown,bottomup)-regression-quadratic"
                  ((cbv [nat_rect List.repeat]);
                   repeat (cbn [list_rect];
                           (rewrite_strat ((try repeat topdown hints mydb1); (try repeat bottomup hints mydb2)))))
     | kind_rewrite_strat bottomup_bottomup
       => fun nm
          => time "rewrite_strat(bottomup,bottomup)"
                  ((cbv [nat_rect List.repeat]);
                   repeat (cbn [list_rect];
                           (rewrite_strat ((try repeat bottomup hints mydb1); (try repeat bottomup hints mydb2)))))
     | kind_setoid_rewrite
       => fun nm
          => time "setoid_rewrite"
                  (cbv [nat_rect List.repeat];
                   repeat (cbn [list_rect];
                           repeat setoid_rewrite lift_let_cons;
                           repeat setoid_rewrite lift_let_list_rect))
     | kind_red vm
       => fun nm
          => time "cps+vm_compute" vm_compute
     | kind_red native
       => fun nm
          => time "cps+native_compute" native_compute
     | kind_red cbv
       => fun nm
          => time "cps+cbv" cbv
     | kind_red lazy
       => fun nm
          => time "cps+lazy" lazy
     | kind_red cbn
       => fun nm
          => time "cps+cbn" cbn
     | kind_red simpl
       => fun nm
          => time "cps+simpl" simpl
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

Hint Opaque Let_In : rewrite typeclass_instances.
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
