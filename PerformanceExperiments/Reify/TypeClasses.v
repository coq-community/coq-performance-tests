(** * Typeclass-based reification *)
Require Import Reify.ReifyCommon.
Require Import Coq.NArith.NArith.
Require Import PerformanceExperiments.Harness.
Require Import Reify.BenchmarkExtraUtil.

Module TypeClasses.
  Local Generalizable Variables x y rx ry f rf.
  Section with_var.
    Context {var : Type}.

    Class reify_of (term : nat) (rterm : @expr var) := {}.
    Global Program Instance reify_NatMul `{reify_of x rx, reify_of y ry}
      : reify_of (x * y) (rx * ry).
    Global Program Instance reify_LetIn `{reify_of x rx}
            `{forall y ry, reify_of y (Var ry) -> reify_of (f y) (rf ry)}
      : reify_of (dlet y := x in f y) (elet ry := rx in rf ry).
    Global Program Instance reify_S `{reify_of x rx}
      : reify_of (S x) (NatS rx).
    Global Program Instance reify_O
      : reify_of O NatO.
  End with_var.

  (** This must be commented out pre-8.6; it tells Coq to not try to
    infer reifications if it doesn't fully know what term it's
    reifying. *)

  Hint Mode reify_of - ! - : typeclass_instances.
  Hint Opaque Nat.mul Let_In : typeclass_instances.

  Ltac reify var x :=
    let c := constr:(_ : @reify_of var x _) in
    lazymatch type of c with
    | reify_of _ ?rx => rx
    end.

  Ltac Reify x :=
    let c := constr:(fun var => (_ : @reify_of var x _)) in
    lazymatch type of c with
    | forall var, reify_of _ (@?rx var) => rx
    end.

  Ltac do_Reify_rhs
       do_trans
       restart_timer_norm_reif finish_timing_norm_reif
       restart_timer_actual_reif finish_timing_actual_reif
       restart_timer_eval_lazy finish_timing_eval_lazy
       time_lazy_beta_iota time_transitivity_Denote_rv
       _ :=
    do_Reify_rhs_of
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      time_lazy_beta_iota time_transitivity_Denote_rv
      Reify ().
  Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac Reify_rhs
       do_trans
       restart_timer_norm_reif finish_timing_norm_reif
       restart_timer_actual_reif finish_timing_actual_reif
       restart_timer_eval_lazy finish_timing_eval_lazy
       time_lazy_beta_iota time_transitivity_Denote_rv
       _ :=
    Reify_rhs_of
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      time_lazy_beta_iota time_transitivity_Denote_rv
      Reify ().
End TypeClasses.

Module TypeClassesBodyHOAS.
  (** We can also do typeclass-based reification where we return the
      reified term in the body rather than in the type.  However, this
      method does not work well with PHOAS binders, because there's no
      easy way to eliminate the dependency on the unreified binder
      when reifying to PHOAS. *)

  Local Generalizable Variables x y rx ry f rf.
  Class reify_of (term : nat) := rterm : @expr nat.

  (** We use [| 100] so this gets triggered late. *)

  Global Instance reify_Var {x} : reify_of x | 100 := Var x.
  Global Instance reify_NatMul `{rx : reify_of x, ry : reify_of y}
    : reify_of (x * y) := (rx * ry)%expr.
  Global Instance reify_S `{rx : reify_of x}
    : reify_of (S x) := NatS rx.
  Global Instance reify_O
    : reify_of O := NatO.
  Global Instance reify_LetIn `{rx : reify_of x}
         `{rf : forall y, reify_of (f y)}
    : reify_of (dlet y := x in f y) := (elet ry := rx in rf ry)%expr.

  (** This must be commented out pre-8.6; it tells Coq to not try to
    infer reifications if it doesn't fully know what term it's
    reifying. *)

  Hint Mode reify_of ! : typeclass_instances.
  Hint Opaque Nat.mul Let_In : typeclass_instances.

  Ltac Reify x :=
    constr:(_ : @reify_of x).

  Ltac do_Reify_rhs
       do_trans
       restart_timer_norm_reif finish_timing_norm_reif
       restart_timer_actual_reif finish_timing_actual_reif
       restart_timer_eval_lazy finish_timing_eval_lazy
       time_lazy_beta_iota time_transitivity_Denote_rv
       _ :=
    do_Reify_rhs_of_with_denote
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      time_lazy_beta_iota time_transitivity_Denote_rv
      Reify denote ().
  Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac Reify_rhs
       do_trans
       restart_timer_norm_reif finish_timing_norm_reif
       restart_timer_actual_reif finish_timing_actual_reif
       restart_timer_eval_lazy finish_timing_eval_lazy
       time_lazy_beta_iota time_transitivity_Denote_rv
       _ :=
    Reify_rhs_of
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      time_lazy_beta_iota time_transitivity_Denote_rv
      Reify ().
End TypeClassesBodyHOAS.

Module TypeClassesBodyFlatPHOAS.
  (** We can also do typeclass-based reification where we return the
      reified term in the body rather than in the type.  However, this
      method does not work well with binders, because there's no easy
      way to eliminate the dependency on the unreified binder when
      reifying to PHOAS. *)

  Local Generalizable Variables x y rx ry f rf.
  Section with_var.
    Context {var : Type}.

    Class reify_of (term : nat) := rterm : @expr var.
    Global Instance reify_NatMul `{rx : reify_of x, ry : reify_of y}
      : reify_of (x * y) := (rx * ry)%expr.
    Global Instance reify_S `{rx : reify_of x}
      : reify_of (S x) := NatS rx.
    Global Instance reify_O
      : reify_of O := NatO.
  End with_var.

  (** This must be commented out pre-8.6; it tells Coq to not try to
    infer reifications if it doesn't fully know what term it's
    reifying. *)

  Hint Mode reify_of - ! : typeclass_instances.
  Hint Opaque Nat.mul : typeclass_instances.

  Ltac reify var x :=
    constr:(_ : @reify_of var x).

  Ltac Reify x :=
    constr:(_ : forall var, @reify_of var x).

  Ltac do_Reify_rhs
       do_trans
       restart_timer_norm_reif finish_timing_norm_reif
       restart_timer_actual_reif finish_timing_actual_reif
       restart_timer_eval_lazy finish_timing_eval_lazy
       time_lazy_beta_iota time_transitivity_Denote_rv
       _ :=
    do_Reify_rhs_of
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      time_lazy_beta_iota time_transitivity_Denote_rv
      Reify ().
  Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac Reify_rhs
       do_trans
       restart_timer_norm_reif finish_timing_norm_reif
       restart_timer_actual_reif finish_timing_actual_reif
       restart_timer_eval_lazy finish_timing_eval_lazy
       time_lazy_beta_iota time_transitivity_Denote_rv
       _ :=
    Reify_rhs_of
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      time_lazy_beta_iota time_transitivity_Denote_rv
      Reify ().
End TypeClassesBodyFlatPHOAS.

Global Open Scope N_scope.

Inductive kind := BodyFlatPHOAS | ArgPHOAS (is_flat : bool) | BodyHOAS (is_flat : bool).
Inductive representation_kind := PHOAS | HOAS.
Definition is_flat (k : kind) : bool
  := match k with
     | BodyFlatPHOAS => true
     | ArgPHOAS is_flat => is_flat
     | BodyHOAS is_flat => is_flat
     end.
Definition representation (k : kind) : representation_kind
  := match k with
     | BodyFlatPHOAS => PHOAS
     | ArgPHOAS _ => PHOAS
     | BodyHOAS _ => HOAS
     end.

Definition args_of_size (k : kind) (s : size) : list N
  := match representation k, is_flat k, s with
     | _    , _    , Sanity => List.firstn 4 sequence
     | PHOAS, true , SuperFast => args_of_max_n   300
     | PHOAS, true , Fast      => args_of_max_n  6000
     | PHOAS, true , Medium    => args_of_max_n 30000
     | PHOAS, false, SuperFast => args_of_max_n    40
     | PHOAS, false, Fast      => args_of_max_n    85
     | PHOAS, false, Medium    => args_of_max_n   300
     | PHOAS, _    , _         => args_of_max_n 30000
     | HOAS , true , SuperFast => args_of_max_n   300
     | HOAS , true , Fast      => args_of_max_n  6000
     | HOAS , true , Medium    => args_of_max_n 30000
     | HOAS , false, SuperFast => args_of_max_n   185
     | HOAS , false, Fast      => args_of_max_n   375
     | HOAS , false, Medium    => args_of_max_n  2000
     | HOAS , _    , _         => args_of_max_n 30000
     end.

Ltac mkgoal kind := let is_flat := (eval cbv in (is_flat kind)) in BenchmarkExtraUtil.mkgoal is_flat (* n *).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.
Ltac time_solve_goal kind sz :=
  let kind := (eval cbv in kind) in
  let is_flat := (eval cbv in (is_flat kind)) in
  let representation := (eval cbv in (representation kind)) in
  let do_cbv := BenchmarkExtraUtil.do_cbv in
  let do_trans := (eval lazy in (do_trans_of_size sz)) in
  let pre_reify := BenchmarkExtraUtil.noop in
  let do_reify := lazymatch kind with
                  | BodyFlatPHOAS => TypeClassesBodyFlatPHOAS.do_Reify_rhs do_trans
                  | ArgPHOAS _ => TypeClasses.do_Reify_rhs do_trans
                  | BodyHOAS _ => TypeClassesBodyHOAS.do_Reify_rhs do_trans
                  end in
  let post_reify := lazymatch kind with
                    | BodyFlatPHOAS => TypeClassesBodyFlatPHOAS.post_Reify_rhs do_trans
                    | ArgPHOAS _ => TypeClasses.post_Reify_rhs do_trans
                    | BodyHOAS _ => TypeClassesBodyHOAS.post_Reify_rhs do_trans
                    end in
  lazymatch kind with
  | BodyFlatPHOAS
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic" do_reify   x in
       let post_reify x := time "post for TypeClassesBodyFlatPHOAS with big_flat-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | ArgPHOAS true
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for TypeClassesPHOAS with big_flat-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for TypeClassesPHOAS with big_flat-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for TypeClassesPHOAS with big_flat-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for TypeClassesPHOAS with big_flat-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for TypeClassesPHOAS with big_flat-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for TypeClassesPHOAS with big_flat-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for TypeClassesPHOAS with big_flat-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for TypeClassesPHOAS with big_flat-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for TypeClassesPHOAS with big_flat-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for TypeClassesPHOAS with big_flat-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for TypeClassesPHOAS with big_flat-regression-quadratic" do_reify   x in
       let post_reify x := time "post for TypeClassesPHOAS with big_flat-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | ArgPHOAS false
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for TypeClassesPHOAS with big-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for TypeClassesPHOAS with big-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for TypeClassesPHOAS with big-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for TypeClassesPHOAS with big-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for TypeClassesPHOAS with big-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for TypeClassesPHOAS with big-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for TypeClassesPHOAS with big-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for TypeClassesPHOAS with big-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for TypeClassesPHOAS with big-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for TypeClassesPHOAS with big-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for TypeClassesPHOAS with big-regression-quadratic" do_reify   x in
       let post_reify x := time "post for TypeClassesPHOAS with big-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | BodyHOAS true
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for TypeClassesBodyHOAS with big_flat-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for TypeClassesBodyHOAS with big_flat-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for TypeClassesBodyHOAS with big_flat-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for TypeClassesBodyHOAS with big_flat-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for TypeClassesBodyHOAS with big_flat-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for TypeClassesBodyHOAS with big_flat-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for TypeClassesBodyHOAS with big_flat-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for TypeClassesBodyHOAS with big_flat-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for TypeClassesBodyHOAS with big_flat-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for TypeClassesBodyHOAS with big_flat-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for TypeClassesBodyHOAS with big_flat-regression-quadratic" do_reify   x in
       let post_reify x := time "post for TypeClassesBodyHOAS with big_flat-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | BodyHOAS false
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for TypeClassesBodyHOAS with big-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for TypeClassesBodyHOAS with big-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for TypeClassesBodyHOAS with big-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for TypeClassesBodyHOAS with big-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for TypeClassesBodyHOAS with big-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for TypeClassesBodyHOAS with big-regression-quadratic") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for TypeClassesBodyHOAS with big-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for TypeClassesBodyHOAS with big-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for TypeClassesBodyHOAS with big-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for TypeClassesBodyHOAS with big-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for TypeClassesBodyHOAS with big-regression-quadratic" do_reify   x in
       let post_reify x := time "post for TypeClassesBodyHOAS with big-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | ?kind => fail 0 "Unrecognized kind:" kind
  end.

Ltac do_verify kind :=
  let is_flat := (eval cbv in (is_flat kind)) in
  BenchmarkExtraUtil.do_verify is_flat.

(**
<<<

#!/usr/bin/env python3

print(r'''(**
<<<
''')
print(open(__file__, 'r').read())
print(r'''>>>
 *)''')

for i, kind in enumerate(('BodyFlatPHOAS', 'ArgPHOAS true', 'ArgPHOAS false', 'BodyHOAS true', 'BodyHOAS false')):
    print(f'Ltac mkgoal{i} := mkgoal constr:({kind}).\nLtac time_solve_goal{i} := time_solve_goal constr:({kind}).\nLtac verify{i} := do_verify constr:({kind}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size ({kind})) describe_goal mkgoal{i} redgoal ltac:(time_solve_goal{i} sz) verify{i} sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:(BodyFlatPHOAS).
Ltac time_solve_goal0 := time_solve_goal constr:(BodyFlatPHOAS).
Ltac verify0 := do_verify constr:(BodyFlatPHOAS).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size (BodyFlatPHOAS)) describe_goal mkgoal0 redgoal ltac:(time_solve_goal0 sz) verify0 sz.

Ltac mkgoal1 := mkgoal constr:(ArgPHOAS true).
Ltac time_solve_goal1 := time_solve_goal constr:(ArgPHOAS true).
Ltac verify1 := do_verify constr:(ArgPHOAS true).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size (ArgPHOAS true)) describe_goal mkgoal1 redgoal ltac:(time_solve_goal1 sz) verify1 sz.

Ltac mkgoal2 := mkgoal constr:(ArgPHOAS false).
Ltac time_solve_goal2 := time_solve_goal constr:(ArgPHOAS false).
Ltac verify2 := do_verify constr:(ArgPHOAS false).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size (ArgPHOAS false)) describe_goal mkgoal2 redgoal ltac:(time_solve_goal2 sz) verify2 sz.

Ltac mkgoal3 := mkgoal constr:(BodyHOAS true).
Ltac time_solve_goal3 := time_solve_goal constr:(BodyHOAS true).
Ltac verify3 := do_verify constr:(BodyHOAS true).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size (BodyHOAS true)) describe_goal mkgoal3 redgoal ltac:(time_solve_goal3 sz) verify3 sz.

Ltac mkgoal4 := mkgoal constr:(BodyHOAS false).
Ltac time_solve_goal4 := time_solve_goal constr:(BodyHOAS false).
Ltac verify4 := do_verify constr:(BodyHOAS false).
Ltac run4 sz := Harness.runtests_verify_sanity (args_of_size (BodyHOAS false)) describe_goal mkgoal4 redgoal ltac:(time_solve_goal4 sz) verify4 sz.

Global Open Scope N_scope.

(*
Goal True.
  run4 Sanity.
*)
