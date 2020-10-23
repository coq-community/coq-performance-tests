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
Local Existing Instance Sample.Z_prod_has_min.

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
     | kind_rewrite_strat bottomup_bottomup
       => 1.69E-03 + -2.38E-03*x + 4.42E-03*x^2
     | kind_rewrite_strat topdown_bottomup
       => -4.52E-03 + -7.08E-03*x + 6.03E-03*x^2
     | kind_setoid_rewrite
       => 1.07 + -0.667*x + 0.0946*x^2
     | kind_red vm
       => 5.02E-04 + 3.53E-06*x + 3.44E-10*x^2
     | kind_red native
       => 0.113 + -7.58E-06*x + 8.72E-10*x^2
     | kind_red cbv
       => -9.57E-04 + 3.73E-06*x + 4.99E-11*x^2
     | kind_red lazy
       => -1.57E-04 + 2.67E-06*x + 2.34E-10*x^2
     | kind_red cbn
       => -0.0378 + 3.86E-04*x + 5.35E-07*x^2
     | kind_red simpl
       => 2.42E-03 + -1.81E-03*x + 3.23E-04*x^2
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
       => Some (130, 130) (* stack overflows on (20880, 1) *)
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
                         Qstandard_max_seconds
                         Sample.default_max_points
                         (max_input_of_kind k'))
                   k)
        s.
Local Set NativeCompute Profiling.
Local Set NativeCompute Timing.
Time Definition args_of_size := args_of_size' (*(k : kind_of_rewrite) (s : size)
  := Eval native_compute in eta_size (s' => eta_kind (k' => N.of_nat (List.length (args_of_size' k' s'))) k) s*).
(*
Goal True.
  pose (fun k s => eta_size (s' => eta_kind (k' => N.of_nat (List.length (args_of_size' k' s'))) k) s) as v.
  cbv [args_of_size'] in v.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  Time vm_compute in k; subst k.
  set (k := (N.of_nat _)) in (value of v) at 1.
  clear v.
  cbv [Sample.generate_inputs] in k.
  (*set (attae := Sample.adjusted_total_time_all_elems_T) in (value of k).*)
  cbv [Sample.total_time_of_Z_prod_poly] in k.
  set (tbl := Sample.small_table_rev_cached) in (value of k).
  vm_compute in tbl.
  set (z := max_input_of_kind _) in (value of k).
  vm_compute in z; subst z.
  vm_compute option_map in k.
  cbv beta iota in k.
  cbv [Sample.binary_alloc] in k.
  set (fuel := Nat.add _ _) in (value of k).
  vm_compute in fuel.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.binary_alloc_QT_fueled] in k.
  set (v := Sample.count_elems_T _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  set (v := N.eqb _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  cbv beta iota zeta in k.
  set (v := N.eqb _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  cbv beta iota zeta in k.
  set (v := orb _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  cbv beta iota zeta in k.
  set (v := orb _ _) in (value of k) at 1.
  Time vm_compute in v; subst v; cbv beta iota zeta in k.
  set (v := Qred _) in (value of k); vm_compute in v; subst v.
  vm_compute Sample.avg_T in k.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.binary_alloc_QT_fueled] in k.
  set (v := Sample.count_elems_T _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  Time do 1 match (eval cbv delta [k] in k) with
         | context[if ?e then _ else _] => set (v := e) in (value of k); vm_compute in v; subst v; cbv beta iota zeta in k
  end.
  set (v := N.eqb _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  cbv beta iota zeta in k.
  set (v := orb _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  cbv beta iota zeta in k.
  Time do 1 match (eval cbv delta [k] in k) with
         | context[if ?e then _ else _] => set (v := e) in (value of k); vm_compute in v; subst v; cbv beta iota zeta in k
  end.
  Time do 1 match (eval cbv delta [k] in k) with
         | context[if ?e then _ else _] => set (v := e) in (value of k); vm_compute in v; subst v; cbv beta iota zeta in k
  end.
  Time do 1 match (eval cbv delta [k] in k) with
         | context[if ?e then _ else _] => set (v := e) in (value of k); vm_compute in v; subst v; cbv beta iota zeta in k
  end.
  set (v := Qred _) in (value of k); vm_compute in v; subst v.
  vm_compute Sample.avg_T in k.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  Compute (fun x => Qround.Qfloor (1/2 + x*1000) # 1000)
          (Qred ((@Sample.adjusted_size_T
                    (Z * Z)
                    (size_of_kind (kind_red vm))) (95,96))).
  Set Printing Implicit.
  cbn [Sample.binary_alloc_QT_fueled] in k.
  set (v := Sample.count_elems_T _ _) in (value of k) at 1.
  Time vm_compute in v.
  subst v.
  Time do 2 match (eval cbv delta [k] in k) with
         | context[if ?e then _ else _] => set (v := e) in (value of k); vm_compute in v; subst v; cbv beta iota zeta in k
  end.
  set (v := Sample.binary_alloc_QT_fueled _ _ _ _ _ _ _ _ _) in (value of k) at 1.
  time vm_compute in v.
  Time vm_compute in k.
  set (v := Sample.adjusted_total_time_all_elems_T _ _) in (value of k) at 1.

  Time vm_compute in v.
  cbv [Sample.adjusted_total_time_all_elems_T] in v.
  cbv [Sample.total_time_all_elems_T] in v.
  cbv [Let_In Sample.total_time_of_Z_prod_poly_cached] in v.
  cbv [Sample.total_time_of_N_prod_poly_cached] in v.
  vm_compute Z.to_N in v.
  vm_compute Sample.integrate_poly in v.
  cbv beta iota zeta in v.
  Time vm_compute N.leb in v.
  cbv beta iota zeta in v.
  Time vm_compute (Qeq_bool _ _) in v.
  cbv beta iota zeta in v.
  Time vm_compute Sample.total_time_of_cached_table in v.
  time vm_compute Sample.Qln in v.
  Time vm_compute Sample.eval_poly in v.
  clear -v.
  Ltac redify x :=
    let recr2 op x y := let x := redify x in let y := redify y in constr:(Qred (op x y)) in
    lazymatch x with
    | ?x # ?y => constr:(Qred (x # y))
    | Qplus ?x ?y => recr2 Qplus x y
    | Qminus ?x ?y => recr2 Qminus x y
    | Qmult ?x ?y => recr2 Qmult x y
    | ?f ?x => let f := redify f in let x := redify x in constr:(f x)
    | _ => x
    end.
  let v := (eval cbv delta [v] in v) in
  let v := redify v in
  pose v as v'.
  Time vm_compute in v'.
  Time vm_compute in v.
  Time vm_compute in v.
  Time vm_compute in v.
  pose (Qred v) as v'.
  Time vm_compute in v'.
  Time vm_compute in v.
  pose (Qred v) as v'.
  Time vm_compute in v'.
  subst v.
  clear -v'.
  cbv [Sample.adjusted_total_time_all_elems_T] in v'.
  cbv [Sample.total_time_all_elems_T] in v'.
  cbv [Sample.total_time_of_Z_prod_poly] in v'.
  cbv [Sample.total_time_of_N_prod_poly] in v'.
  Time vm_compute Sample.integrate_poly in v'.
  cbv beta iota zeta in v'.
  Time vm_compute N.leb in v'.
  Time vm_compute Qeq_bool in v'.
  cbv beta iota zeta in v'.
  Time vm_compute Qeq_bool in v'.
  cbv beta iota zeta in v'.
  set (v'' := Qeq_bool _ _) in (value of v') at 1; vm_compute in v''; subst v''.
  set (v'' := Qeq_bool _ _) in (value of v') at 1; vm_compute in v''; subst v''.
  cbv beta iota zeta in v'.
  set (v'' := fold_right _ _ _) in (value of v') at 1.
  vm_compute Z.to_nat in v''.
  Time vm_compute in v''.
  subst v''.
  Time vm_compute in v'.
  pose (Qred (fold_right (fun x y => Qred (Qplus (x) (y))) 0%Q
           (map
              (fun '(i, count) =>
               ((inject_Z count * Sample.adjusted_size_T (size:=(fun '(x, y) => size_of_kind (kind_red vm) (Z.of_N x, Z.of_N y))) (1%N, i)))%Q)
              (skipn 1 Sample.small_table)))) as v'''.
  Time vm_compute in v'''.
  subst v''.
  vm_compute
  Time vm_compute in v'.
  Time vm_compute in v'.
  Time vm_compute in v.
  Time repeat match (eval cbv delta [k] in k) with
         | context[if ?e then _ else _] => set (v := e) in (value of k); vm_compute in v; subst v; cbv beta iota zeta in k
  end.

  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  let f := (eval vm_compute in (pred fuel)) in set (fuel' := f) in (value of fuel); subst fuel; rename fuel' into fuel.
  cbn [Sample.find_above_max_size] in z.
  vm_compute Qle_bool in z.
  cbv beta iota in z.
  set (w := Sample.double_T _) in (value of z) at 1; vm_compute in w; subst w.
  set (w := Sample.double_T _) in (value of z) at 1; vm_compute in w; subst w.
  vm_compute Qstandard_max_seconds in z.

  vm_compute size_of_kind in z.

  set (fuel' :=
  cbv [Sample.find_above_max_size] in z.
  vm_compute in z; subst z.
  cbv beta iota in k.
  vm_compute Sample.min_T in k.
  Time vm_compute in k; subst k.

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
*)
