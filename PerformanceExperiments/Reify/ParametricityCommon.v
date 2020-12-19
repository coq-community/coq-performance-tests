(** * Reification by parametricity *)
Require Import Reify.ReifyCommon.

Ltac Reify x :=
  let rx := lazymatch (eval pattern (nat : Type), O, S, Nat.mul, (@Let_In nat nat) in x) with
            | ?rx _ _ _ _ _ => rx end in
  let __ := type of rx in (* propagate universe constraints, c.f., https://github.com/coq/coq/issues/5996 *)
  constr:(fun var : Type => rx (@expr var) (@NatO var) (@NatS var) (@NatMul var)
                               (fun x' f' => @LetIn var x' (fun v => f' (@Var var v)))).

Ltac reify var x :=
  let rx := Reify x in
  constr:(rx var).

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
