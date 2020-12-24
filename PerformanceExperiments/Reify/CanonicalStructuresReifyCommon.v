(** * Reification by canonical structures *)
Require Import Reify.Common.
Require Export Reify.ReifyCommon.
Require Import Reify.PHOAS.

(** Take care of initial locking of mul, letin, etc. *)

Ltac make_pre_Reify_rhs nat_of untag do_lock_letin do_lock_natmul :=
  let RHS := lazymatch goal with |- _ = ?RHS => RHS end in
  let e := fresh "e" in
  let T := fresh in
  evar (T : Type);
  evar (e : T);
  subst T;
  cut (untag (nat_of e) = RHS);
  [ subst e
  | lazymatch do_lock_letin with
    | true => rewrite ?lock_Let_In_nat
    | false => idtac
    end;
    lazymatch do_lock_natmul with
    | true => rewrite ?lock_Nat_mul
    | false => idtac
    end;
    cbv [e]; clear e ].

(** N.B. we must thunk the constants so as to not focus the goal *)

Ltac make_do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     denote reified_nat_of postprocess :=
  [ >
  | crun restart_timer_norm_reif (*restart_timer "norm reif"*);
    crun restart_timer_actual_reif;
    (*time "actual reif"*) refine eq_refl ];
  let __ := crun finish_timing_actual_reif in
  let denote := denote () in
  let reified_nat_of := reified_nat_of () in
  let e := lazymatch goal with |- ?untag (?nat_of ?e) = _ -> ?LHS = _ => e end in
  let __ := crun restart_timer_eval_lazy (*ltac:(restart_timer "eval lazy")*) in
  let e' := (eval lazy in (reified_nat_of e)) in
  let __ := crun finish_timing_eval_lazy (*ltac:(finish_timing ("Tactic call") "eval lazy")*) in
  let __ := crun restart_timer_postprocess (*ltac:(restart_timer "postprocess")*) in
  let e' := postprocess e' in
  let __ := crun finish_timing_postprocess (*ltac:(finish_timing ("Tactic call") "postprocess")*) in
  let __ := crun finish_timing_norm_reif (*ltac:(finish_timing ("Tactic call") "norm reif")*) in
  time_intros_ (*time "intros _"*) ltac:(intros _);
  time_lazy_beta_iota (*time "lazy beta iota"*) ltac:(lazy beta iota);
  if_doing_trans
    do_trans
         ltac:(fun _
               => time_transitivity_Denote_rv (*time "transitivity (Denote rv)"*)
                    ltac:(transitivity (denote e'))).
