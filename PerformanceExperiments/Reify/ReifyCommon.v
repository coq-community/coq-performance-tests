(** * Factored code common to many variants of reification *)
Require Export Reify.Common.
Require Export Reify.PHOAS.

(** We provide a tactic to run a tactic in a constr context. *)

Ltac crun tac :=
  match goal with
  | _ => tac
  end.

(** Note: If you want to preserve variable names on reification, there
    are many hoops to jump through. We write a [refresh] tactic which
    permits preserving binder names at a nontrivial performance
    overhead. *)

(** c.f. %\url{https://github.com/coq/coq/issues/5448}%,
         %\url{https://github.com/coq/coq/issues/6315}%,
         %\url{https://github.com/coq/coq/issues/6559}% *)

Ltac require_same_var n1 n2 :=
  let c1 := constr:(fun n1 n2 : Set => ltac:(exact n1)) in
  let c2 := constr:(fun n1 n2 : Set => ltac:(exact n2)) in
  first [ constr_eq c1 c2
        | fail 1 "Not the same var:" n1 "and" n2 "(via constr_eq" c1 c2 ")" ].
Ltac is_same_var n1 n2 :=
  match goal with
  | _ => let __ := match goal with _ => require_same_var n1 n2 end in
         true
  | _ => false
  end.
Ltac is_underscore v :=
  let v' := fresh v in
  let v' := fresh v' in
  is_same_var v v'.

(** Note that [fresh_tac] must be [ltac:(fun n => fresh n)];
    c.f. %\url{https://github.com/coq/coq/issues/6559}% *)

Ltac refresh n fresh_tac :=
  let n_is_underscore := is_underscore n in
  let n' := lazymatch n_is_underscore with
            | true => fresh
            | false => fresh_tac n
            end in
  let n' := fresh_tac n' in
  n'.

(** However, this comes at a significant cost in speed, so we do not
    try to preserve variable names, and this tactic is unused in our
    benchmark. *)

Ltac Reify_of reify x :=
  constr:(fun var : Type => ltac:(let v := reify var x in exact v)).

Ltac if_doing_trans do_trans tac :=
  lazymatch do_trans with
  | true => tac ()
  | false => idtac
  end.

(** We ask for dummy arguments for most things, because it is good
    practice to indicate that this tactic should not be run at the
    call-site (when it's passed to another tactic), but at the
    use-site. *)

Ltac do_Reify_rhs_of_cps_with_denote
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify_cps Denote _ :=
  let v := lazymatch goal with |- ?LHS = ?v => v end in
  let __ := crun restart_timer_norm_reif (*ltac:(restart_timer "norm reif")*) in
  let __ := crun restart_timer_actual_reif (*ltac:(restart_timer "actual reif")*) in
  Reify_cps v ltac:(
    fun rv
    => let __ := crun finish_timing_actual_reif (*ltac:(finish_timing ("Tactic call") "actual reif")*) in
       let __ := crun restart_timer_eval_lazy (*ltac:(restart_timer "eval lazy")*) in
       let rv := (eval lazy in rv) in
       let __ := crun finish_timing_eval_lazy (*ltac:(finish_timing ("Tactic call") "eval lazy")*) in
       let __ := crun finish_timing_norm_reif (*ltac:(finish_timing ("Tactic call") "norm reif")*) in
       time_lazy_beta_iota (*time "lazy beta iota"*) ltac:(lazy beta iota);
       if_doing_trans
         do_trans
         ltac:(fun _
               => time_transitivity_Denote_rv (*time "transitivity (Denote rv)"*)
                    ltac:(transitivity (Denote rv)))).
Ltac do_Reify_rhs_of_cps
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify_cps _ :=
  do_Reify_rhs_of_cps_with_denote
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify_cps Denote ().
Ltac do_Reify_rhs_of_with_denote
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify Denote _ :=
  do_Reify_rhs_of_cps_with_denote
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     ltac:(fun v tac => let rv := Reify v in tac rv) Denote ().
Ltac do_Reify_rhs_of
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify _ :=
  do_Reify_rhs_of_with_denote
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify Denote ().
Ltac post_Reify_rhs do_trans _ :=
  [ > ..
  | if_doing_trans do_trans ltac:(fun _ => lazy [Denote denote]; reflexivity) ].
Ltac Reify_rhs_of_cps
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify_cps _ :=
  do_Reify_rhs_of_cps
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify_cps ();
  post_Reify_rhs do_trans ().
Ltac Reify_rhs_of
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify _ :=
  do_Reify_rhs_of
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     time_lazy_beta_iota time_transitivity_Denote_rv
     Reify ();
  post_Reify_rhs do_trans ().

Ltac error_cant_elim_deps f :=
  let __ := match goal with
            | _ => idtac "Failed to eliminate functional dependencies in" f
            end in
  constr:(I : I).

Ltac error_bad_function f :=
  let __ := match goal with
            | _ => idtac "Bad let-in function" f
            end in
  constr:(I : I).

Ltac error_bad_term term :=
  let __ := match goal with
            | _ => idtac "Unrecognized term:" term
            end in
  let ret := constr:(term : I) in
  constr:(I : I).
