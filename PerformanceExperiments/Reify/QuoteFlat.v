(** * Reification by the quote plugin *)
Require Import Coq.quote.Quote.
Require Import Reify.ReifyCommon.
Require Import Coq.NArith.NArith.
Require Import PerformanceExperiments.Harness.
Require Import Reify.BenchmarkExtraUtil.

Inductive qexpr : Set :=
| qNatO : qexpr
| qNatS : qexpr -> qexpr
| qNatMul (x y : qexpr)
| qConst (k : nat).

Module Export Exports.
  Fixpoint qdenote (e : qexpr) : nat
    := match e with
       | qNatO => O
       | qNatS x => S (qdenote x)
       | qNatMul x y => Nat.mul (qdenote x) (qdenote y)
       | qConst k => k
       end.
End Exports.

Fixpoint compile_nat {var} (n : nat) : @expr var
  := match n with
     | O => NatO
     | S x => NatS (compile_nat x)
     end.

Fixpoint compile {var} (e : qexpr) : @expr var
  := match e with
     | qNatO => NatO
     | qNatS x => NatS (compile x)
     | qNatMul x y => NatMul (compile x) (compile y)
     | qConst k => compile_nat k
     end.

Definition Compile (e : qexpr) : Expr := fun var => compile e.

Ltac reify_cps var term tac :=
  quote qdenote [S O] in term using
    (fun v => lazymatch v with qdenote ?v => tac (@compile var v) end).

Ltac Reify_cps term tac :=
  quote qdenote [S O] in term using
    (fun v => lazymatch v with qdenote ?v => tac (@Compile v) end).

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

Definition args_of_size (s : size) : list N
  := match s with
     | Sanity => List.firstn 4 sequence
     | SuperFast => args_of_max_n  1000
     | _         => args_of_max_n 30000
     end.

Ltac mkgoal := BenchmarkExtraUtil.mkgoal true (*is_flat*) (* n *).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.
Ltac time_solve_goal sz :=
  let is_flat := true in
  let do_cbv := BenchmarkExtraUtil.do_cbv in
  let do_trans := (eval lazy in (do_trans_of_size sz)) in
  let pre_reify := BenchmarkExtraUtil.noop in
  let do_reify := do_Reify_rhs do_trans in
  let post_reify := post_Reify_rhs do_trans in
  let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for QuoteFlat with big_flat") in
  let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for QuoteFlat with big_flat") in
  let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for QuoteFlat with big_flat") in
  let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for QuoteFlat with big_flat") in
  let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for QuoteFlat with big_flat") in
  let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for QuoteFlat with big_flat") in
  let time_lazy_beta_iota tac   := time                             "lazy beta iota for QuoteFlat with big_flat" tac in
  let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for QuoteFlat with big_flat" tac in
  let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
  let do_cbv     x := time  "cbv for QuoteFlat with big_flat" do_cbv     x in
  let pre_reify  x := time  "pre for QuoteFlat with big_flat" pre_reify  x in
  let do_reify   x := time "reif for QuoteFlat with big_flat" do_reify   x in
  let post_reify x := time "post for QuoteFlat with big_flat" post_reify x in
  BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify.
Ltac do_verify := BenchmarkExtraUtil.do_verify true (*is_flat*).

Ltac mkgoal0 := mkgoal.
Ltac time_solve_goal0 := time_solve_goal.
Ltac verify0 := do_verify.
Ltac run0 sz := Harness.runtests_verify_sanity args_of_size describe_goal mkgoal0 redgoal ltac:(time_solve_goal0 sz) verify0 sz.

Global Open Scope N_scope.
(*
Goal True.
  run0 SuperFast.
*)
