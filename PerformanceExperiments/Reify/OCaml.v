(** * Reification in OCaml *)
Require Import Reify.ReifyCommon.
Require Import Reify.OCamlReify.
From Coq Require Import NArith.
Require Import PerformanceExperiments.Harness.
Require Import Reify.BenchmarkExtraUtil.
(** See [OCamlReify.v] and [reify_plugin.{ml4,mlg}] for the implementation code. *)

Ltac Reify_cps term tac :=
  quote_term_cps
    [var, Type] (@Var) (@NatO) (@NatS) (@NatMul) (@LetIn) O S Nat.mul (@Let_In)
    term tac.

Ltac reify_cps var term tac :=
  Reify_cps term ltac:(fun rt => tac (rt var)).

Ltac do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
  do_Reify_rhs_of_cps
    do_trans
    restart_timer_norm_reif finish_timing_norm_reif
    restart_timer_actual_reif finish_timing_actual_reif
    restart_timer_eval_lazy finish_timing_eval_lazy
    time_lazy_beta_iota time_transitivity_Denote_rv
    Reify_cps ().
Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
Ltac Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
  Reify_rhs_of_cps
    do_trans
    restart_timer_norm_reif finish_timing_norm_reif
    restart_timer_actual_reif finish_timing_actual_reif
    restart_timer_eval_lazy finish_timing_eval_lazy
    time_lazy_beta_iota time_transitivity_Denote_rv
    Reify_cps ().

Definition args_of_size (is_flat : bool) (s : size) : list N
  := match is_flat, s with
     | _, Sanity => List.firstn 4 sequence
     | _, SuperFast => args_of_max_n  1000
     | _, _         => args_of_max_n 30000
     end.

Ltac mkgoal is_flat := BenchmarkExtraUtil.mkgoal is_flat (* n *).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.
Ltac time_solve_goal is_flat sz :=
  let do_cbv := BenchmarkExtraUtil.do_cbv in
  let do_trans := (eval lazy in (do_trans_of_size sz)) in
  let pre_reify := BenchmarkExtraUtil.noop in
  let do_reify := do_Reify_rhs do_trans in
  let post_reify := post_Reify_rhs do_trans in
  lazymatch is_flat with
  | true
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for OCaml with big_flat") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for OCaml with big_flat") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for OCaml with big_flat") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for OCaml with big_flat") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for OCaml with big_flat") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for OCaml with big_flat") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for OCaml with big_flat" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for OCaml with big_flat" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for OCaml with big_flat" do_cbv     x in
       let pre_reify  x := time  "pre for OCaml with big_flat" pre_reify  x in
       let do_reify   x := time "reif for OCaml with big_flat" do_reify   x in
       let post_reify x := time "post for OCaml with big_flat" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | false
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for OCaml with big") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for OCaml with big") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for OCaml with big") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for OCaml with big") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for OCaml with big") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for OCaml with big") in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for OCaml with big" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for OCaml with big" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for OCaml with big" do_cbv     x in
       let pre_reify  x := time  "pre for OCaml with big" pre_reify  x in
       let do_reify   x := time "reif for OCaml with big" do_reify   x in
       let post_reify x := time "post for OCaml with big" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | ?is_flat => fail 0 "Unrecognized value for is_flat (expected true or false):" is_flat
  end.

Ltac do_verify is_flat := BenchmarkExtraUtil.do_verify is_flat.

(**
<<<

#!/usr/bin/env python3

print(r'''(**
<<<
''')
print(open(__file__, 'r').read())
print(r'''>>>
 *)''')

for i, is_flat in enumerate(('true', 'false')):
    print(f'Ltac mkgoal{i} := mkgoal constr:({is_flat}).\nLtac time_solve_goal{i} := time_solve_goal constr:({is_flat}).\nLtac verify{i} := do_verify constr:({is_flat}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size {is_flat}) describe_goal mkgoal{i} redgoal ltac:(time_solve_goal{i} sz) verify{i} sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:(true).
Ltac time_solve_goal0 := time_solve_goal constr:(true).
Ltac verify0 := do_verify constr:(true).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size true) describe_goal mkgoal0 redgoal ltac:(time_solve_goal0 sz) verify0 sz.

Ltac mkgoal1 := mkgoal constr:(false).
Ltac time_solve_goal1 := time_solve_goal constr:(false).
Ltac verify1 := do_verify constr:(false).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size false) describe_goal mkgoal1 redgoal ltac:(time_solve_goal1 sz) verify1 sz.

Global Open Scope N_scope.
(*
Goal True.
  run1 SuperFast.
*)
