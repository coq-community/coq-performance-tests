(** * Recursing under binders with tactics in terms, tracking variables by pairing *)
Require Import Reify.ReifyCommon.
Require Import PerformanceExperiments.PrimitiveProd.
Import PrimitiveProd.Primitive.
Import PrimitiveProd.Primitive.Notations.

(** Points of note:

    - We use primitive projections for pairing to speed up typing.

    - We make sure to fill in all implicit arguments explicitly, to
      minimize the number of evars generated; evars are one of the
      main bottlenecks.

    - We must bind open terms to fresh variable names to work around
      the fact that tactics in terms do not correctly support open
      terms.%\footnote{\url{https://github.com/coq/coq/issues/3248}}%

    - We make use of a trick from "%[coqdev]% beta1 and zeta1
      reduction"%\footnote{\url{https://sympa.inria.fr/sympa/arc/coqdev/2016-01/msg00060.html}}%
      to bind names with a single-branch [match] statement without
      incurring extra β or ζ reductions.

    - We must unfold aliases bound with this [match] statement trick
      (substitution does not happen until after typechecking), and if
      we are not careful with how we use [fresh], Coq will stack
      overflow on [cbv delta] or otherwise misbehave.%\footnote{See
      \url{https://github.com/coq/coq/issues/5448},
      \url{https://github.com/coq/coq/issues/6315},
      \url{https://github.com/coq/coq/issues/6559}.}%

    - We give the [return] clause on the [match] statement explicitly.
      Without the explicit return clause, Coq would backtrack on
      failure and attempt a second way of elaborating the [match]
      branches, resulting in a blowup on failure that is exponential
      in the recursive depth of the
      failure.%\footnote{\url{https://github.com/coq/coq/issues/6252\#issuecomment-347041995}}%
      If we used [return _], rather than specifying the type
      explicitly, we incur the cost of allocating an additional evar,
      which is linear in the size of the context.  (This performance
      statistic courtesy of conversations with Pierre-Marie Pédrot on
      Coq's gitter.)

    - We explicitly [clear] variable bindings from the context before
      invoking the recursive call, because the cost of evars is
      proportional to the size of the context.  *)

Ltac reify var term :=
  let reify_rec term := reify var term in
  lazymatch term with
  | fst (?term, ?v)
    => constr:(@Var var v)
  | _
    =>
    lazymatch term with
    | O => constr:(@NatO var)
    | S ?x
      => let rx := reify_rec x in
         constr:(@NatS var rx)
    | ?x * ?y
      => let rx := reify_rec x in
         let ry := reify_rec y in
         constr:(@NatMul var rx ry)
    | (dlet x := ?v in ?f)
      => let rv := reify_rec v in
         let not_x := fresh (*x *)in (* don't try to preserve variable names; c.f. comments around ReifyCommon.refresh *)
         let not_x2 := fresh (*not_x *)in (* don't try to preserve variable names; c.f. comments around ReifyCommon.refresh *)
         let not_x3 := fresh (*not_x2 *)in (* don't try to preserve variable names; c.f. comments around ReifyCommon.refresh *)
         let rf
             :=
             lazymatch
               constr:(
                 fun (not_x : nat) (not_x2 : var)
                 => match @fst nat var (@pair nat var not_x not_x2)
                          return @expr var (* c.f. COQBUG(https://github.com/coq/coq/issues/6252#issuecomment-347041995) for [return] *)
                    with
                    | x
                      => match f return @expr var with
                         | not_x3
                           => ltac:(
                                let fx := (eval cbv delta [not_x3 x] in not_x3) in
                                clear x not_x3;
                                let rf := reify_rec fx in
                                exact rf)
                         end
                    end)
             with
             | fun _ => ?f => f
             | ?f => error_cant_elim_deps f
             end in
         constr:(@LetIn var rv rf)
    | ?v
      => error_bad_term v
    end
  end.

Ltac Reify x := Reify_of reify x.
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
