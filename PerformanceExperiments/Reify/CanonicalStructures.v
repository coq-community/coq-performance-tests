(** * Canonical-structure based reification *)
Require Import Reify.ReifyCommon.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.
Require Import PerformanceExperiments.Harness.
Require Import Reify.BenchmarkExtraUtil.
Require Import Reify.CanonicalStructuresReifyCommon.

Global Set Warnings Append "-projection-no-head-constant".

Module CanonicalStructuresFlatHOAS.
  (** This version reifies to [Expr], and does not support
      let-binders. *)

  (** structure for packaging a nat expr and its reification *)

  Structure tagged_nat := tag { untag :> nat }.
  Structure reified_of :=
    reify { nat_of : tagged_nat ; reified_nat_of :> Expr }.

  (** tags to control the order of application *)

  Definition S_tag := tag.
  Definition O_tag := S_tag.

  (** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)

  Module Export Exports.
    Canonical Structure mul_tag n := O_tag n.
    Canonical Structure reify_O
      := reify (O_tag 0) (@NatO).
    Canonical Structure reify_S x
      := reify (S_tag (S (nat_of x))) (fun var => @NatS var (reified_nat_of x var)).
    Canonical Structure reify_mul x y
      := reify (mul_tag (nat_of x * nat_of y))
               (fun var => @NatMul var (reified_nat_of x var) (reified_nat_of y var)).
  End Exports.

  (** We take advantage of not needing to lock [Let_In] to avoid a
      rewrite by passing [false] to the [do_lock_letin] argument of
      [make_pre_Reify_rhs] *)

  Ltac pre_Reify_rhs _ := make_pre_Reify_rhs nat_of untag false false.

  (** N.B. we must thunk the constants so as to not focus the goal *)

  Ltac do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    make_do_Reify_rhs
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      restart_timer_postprocess finish_timing_postprocess
      time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
      ltac:(fun _ => Denote)
             ltac:(fun _ => reified_nat_of)
                    ltac:(fun x => x).
  Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    pre_Reify_rhs ();
    do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     ();
    post_Reify_rhs do_trans ().
End CanonicalStructuresFlatHOAS.
Export CanonicalStructuresFlatHOAS.Exports.

Module CanonicalStructuresFlatPHOAS.
  (** This version reifies to [Expr], and does not support
      let-binders. *)

  (** structure for packaging a nat expr and its reification *)

  Structure tagged_nat := tag { untag :> nat }.
  Structure reified_of :=
    reify { nat_of : tagged_nat ; reified_nat_of :> Expr }.

  (** tags to control the order of application *)

  Definition S_tag := tag.
  Definition O_tag := S_tag.

  (** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)

  Module Export Exports.
    Canonical Structure mul_tag n := O_tag n.
    Canonical Structure reify_O
      := reify (O_tag 0) (@NatO).
    Canonical Structure reify_S x
      := reify (S_tag (S (nat_of x))) (fun var => @NatS var (reified_nat_of x var)).
    Canonical Structure reify_mul x y
      := reify (mul_tag (nat_of x * nat_of y))
               (fun var => @NatMul var (reified_nat_of x var) (reified_nat_of y var)).
  End Exports.

  (** We take advantage of not needing to lock [Let_In] to avoid a
    rewrite by passing [false] to the [do_lock_letin] argument of
    [make_pre_Reify_rhs] *)

  Ltac pre_Reify_rhs _ := make_pre_Reify_rhs nat_of untag false false.

  (** N.B. we must thunk the constants so as to not focus the goal *)

  Ltac do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    make_do_Reify_rhs
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      restart_timer_postprocess finish_timing_postprocess
      time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
      ltac:(fun _ => Denote)
             ltac:(fun _ => reified_nat_of)
                    ltac:(fun x => x).
  Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    pre_Reify_rhs ();
    do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     ();
    post_Reify_rhs do_trans ().
End CanonicalStructuresFlatPHOAS.
Export CanonicalStructuresFlatPHOAS.Exports.

Module CanonicalStructuresHOAS.
  (** This version reifies to [@expr nat], and supports let-binders. *)

  (** structure for packaging a nat expr and its reification *)

  Structure tagged_nat := tag { untag :> nat }.
  Structure reified_of :=
    reify { nat_of : tagged_nat ; reified_nat_of :> @expr nat }.

  (** tags to control the order of application *)

  Definition var_tag := tag.
  Definition S_tag := var_tag.
  Definition O_tag := S_tag.
  Definition let_in_tag := O_tag.

  (** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)

  Module Export Exports.
    Canonical Structure mul_tag n := let_in_tag n.
    Canonical Structure reify_var n
      := reify (var_tag n) (@Var nat n).
    Canonical Structure reify_O
      := reify (O_tag O) (@NatO nat).
    Canonical Structure reify_S x
      := reify (S_tag (S (nat_of x))) (@NatS nat x).
    Canonical Structure reify_mul x y
      := reify (mul_tag (nat_of x * nat_of y))
               (@NatMul nat x y).
    Canonical Structure reify_let_in v f
      := reify (let_in_tag (nllet x := untag (nat_of v) in nat_of (f x)))
               (elet x := reified_nat_of v in reified_nat_of (f x)).
  End Exports.

  Ltac pre_Reify_rhs _ := make_pre_Reify_rhs nat_of untag true false.

  (** N.B. we must thunk the constants so as to not focus the goal *)

  Ltac do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    make_do_Reify_rhs
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      restart_timer_postprocess finish_timing_postprocess
      time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
      ltac:(fun _ => denote)
             ltac:(fun _ => reified_nat_of)
                    ltac:(fun x => x).
  Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    pre_Reify_rhs ();
    do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     ();
    post_Reify_rhs do_trans ().
End CanonicalStructuresHOAS.
Export CanonicalStructuresHOAS.Exports.

Module CanonicalStructuresPHOAS.
  (** This version reifies to [Expr], and supports let-binders. *)

  Local Notation context := (list nat).

  Structure tagged_nat (ctx : context) := tag { untag :> nat }.

  Structure reified_of (ctx : context) :=
    reify { nat_of : tagged_nat ctx ;
            reified_nat_of :> forall var, list var -> (forall T, T) -> @expr var }.

  Definition var_tl_tag := tag.
  Definition var_hd_tag := var_tl_tag.
  Definition S_tag := var_hd_tag.
  Definition O_tag := S_tag.
  Definition mul_tag := O_tag.

  (** N.B. [Canonical] structures follow [Import], so they must be
    imported for reification to work. *)

  Module Export Exports.
    Canonical Structure letin_tag ctx n := mul_tag ctx n.

    Canonical Structure reify_O ctx
      := reify (O_tag ctx 0) (fun var _ _ => @NatO var).
    Canonical Structure reify_S ctx x
      := reify (@S_tag ctx (S (@nat_of ctx x)))
               (fun var vs phantom => @NatS var (x var vs phantom)).
    Canonical Structure reify_mul ctx x y
      := reify (@mul_tag ctx (@nat_of ctx x * @nat_of ctx y))
               (fun var vs phantom => @NatMul var (x var vs phantom) (y var vs phantom)).
    Canonical Structure reify_var_hd n ctx
      := reify (var_hd_tag (n :: ctx) n)
               (fun var vs phantom => @Var var (List.hd (phantom _) vs)).
    Canonical Structure reify_var_tl n ctx x
      := reify (var_tl_tag (n :: ctx) (@nat_of ctx x))
               (fun var vs phantom => reified_nat_of x (List.tl vs) phantom).
    Canonical Structure reify_letin ctx v f
      := reify (letin_tag
                  ctx
                  (nllet x := @nat_of ctx v in
                         @nat_of (x :: ctx) (f x)))
               (fun var vs phantom
                => elet x := reified_nat_of v vs phantom in
                      reified_nat_of (f (phantom _)) (x :: vs) phantom)%expr.
  End Exports.

  Definition ReifiedNatOf (e : reified_of nil) : (forall T, T) -> Expr
    := fun phantom var => reified_nat_of e nil phantom.

  Ltac pre_Reify_rhs _ := make_pre_Reify_rhs (@nat_of nil) (@untag nil) true false.

  (** N.B. we must thunk the constants so as to not focus the goal *)

  Ltac do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    make_do_Reify_rhs
      do_trans
      restart_timer_norm_reif finish_timing_norm_reif
      restart_timer_actual_reif finish_timing_actual_reif
      restart_timer_eval_lazy finish_timing_eval_lazy
      restart_timer_postprocess finish_timing_postprocess
      time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
      ltac:(fun _ => Denote) ltac:(fun _ => ReifiedNatOf)
                                    ltac:(fun e =>
                                            lazymatch e with
                                            | fun _ => ?e => e
                                            | _ => ReifyCommon.error_cant_elim_deps e
                                            end).
  Ltac post_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     _ :=
    pre_Reify_rhs ();
    do_Reify_rhs
     do_trans
     restart_timer_norm_reif finish_timing_norm_reif
     restart_timer_actual_reif finish_timing_actual_reif
     restart_timer_eval_lazy finish_timing_eval_lazy
     restart_timer_postprocess finish_timing_postprocess
     time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv
     ();
    post_Reify_rhs do_trans ().
End CanonicalStructuresPHOAS.
Export CanonicalStructuresPHOAS.Exports.

Global Open Scope N_scope.

Inductive representation_kind := PHOAS | HOAS.
Record kind := { is_flat : bool ; representation : representation_kind }.

Definition args_of_size (k : kind) (s : size) : list N
  := match k.(representation), k.(is_flat), s with
     | _    , _    , Sanity => List.firstn 4 sequence
     | _, true , SuperFast => args_of_max_n   300
     | _, true , Fast      => args_of_max_n  6000
     | _, true , Medium    => args_of_max_n 30000
     | _, false, SuperFast => args_of_max_n    30
     | _, false, Fast      => args_of_max_n    60
     | _, false, Medium    => args_of_max_n   200
     | _, _    , _         => args_of_max_n 30000
     end.

Ltac mkgoal kind := let is_flat := (eval cbv in kind.(is_flat)) in BenchmarkExtraUtil.mkgoal is_flat (* n *).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.
Ltac time_solve_goal kind sz :=
  let kind := (eval cbv in kind) in
  let is_flat := (eval cbv in kind.(is_flat)) in
  let representation := (eval cbv in kind.(representation)) in
  let do_cbv := BenchmarkExtraUtil.do_cbv in
  let do_trans := (eval lazy in (do_trans_of_size sz)) in
  let pre_reify := lazymatch kind with
                   | {| is_flat := true  ; representation := PHOAS |} => CanonicalStructuresFlatPHOAS.pre_Reify_rhs
                   | {| is_flat := false ; representation := PHOAS |} => CanonicalStructuresPHOAS.pre_Reify_rhs
                   | {| is_flat := true  ; representation :=  HOAS |} => CanonicalStructuresFlatHOAS.pre_Reify_rhs
                   | {| is_flat := false ; representation :=  HOAS |} => CanonicalStructuresHOAS.pre_Reify_rhs
                   end in
  let do_reify := lazymatch kind with
                  | {| is_flat := true  ; representation := PHOAS |} => CanonicalStructuresFlatPHOAS.do_Reify_rhs do_trans
                  | {| is_flat := false ; representation := PHOAS |} => CanonicalStructuresPHOAS.do_Reify_rhs do_trans
                  | {| is_flat := true  ; representation :=  HOAS |} => CanonicalStructuresFlatHOAS.do_Reify_rhs do_trans
                  | {| is_flat := false ; representation :=  HOAS |} => CanonicalStructuresHOAS.do_Reify_rhs do_trans
                  end in
  let post_reify := lazymatch kind with
                    | {| is_flat := true  ; representation := PHOAS |} => CanonicalStructuresFlatPHOAS.post_Reify_rhs do_trans
                    | {| is_flat := false ; representation := PHOAS |} => CanonicalStructuresPHOAS.post_Reify_rhs do_trans
                    | {| is_flat := true  ; representation :=  HOAS |} => CanonicalStructuresFlatHOAS.post_Reify_rhs do_trans
                    | {| is_flat := false ; representation :=  HOAS |} => CanonicalStructuresHOAS.post_Reify_rhs do_trans
                    end in
  lazymatch kind with
  | {| is_flat := true  ; representation := PHOAS |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let restart_timer_postprocess := ltac:(restart_timer                 "postprocess for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let finish_timing_postprocess := ltac:(finish_timing ("Tactic call") "postprocess for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic") in
       let time_intros_ tac          := time                                   "intros _ for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic" tac in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy restart_timer_postprocess finish_timing_postprocess time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic" do_reify   x in
       let post_reify x := time "post for CanonicalStructuresFlatPHOAS with big_flat-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; representation := PHOAS |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let restart_timer_postprocess := ltac:(restart_timer                 "postprocess for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let finish_timing_postprocess := ltac:(finish_timing ("Tactic call") "postprocess for CanonicalStructuresPHOAS with big-regression-quadratic") in
       let time_intros_ tac          := time                                   "intros _ for CanonicalStructuresPHOAS with big-regression-quadratic" tac in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for CanonicalStructuresPHOAS with big-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for CanonicalStructuresPHOAS with big-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy restart_timer_postprocess finish_timing_postprocess time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for CanonicalStructuresPHOAS with big-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for CanonicalStructuresPHOAS with big-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for CanonicalStructuresPHOAS with big-regression-quadratic" do_reify   x in
       let post_reify x := time "post for CanonicalStructuresPHOAS with big-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true  ; representation := HOAS |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let restart_timer_postprocess := ltac:(restart_timer                 "postprocess for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let finish_timing_postprocess := ltac:(finish_timing ("Tactic call") "postprocess for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic") in
       let time_intros_ tac          := time                                   "intros _ for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic" tac in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy restart_timer_postprocess finish_timing_postprocess time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic" do_reify   x in
       let post_reify x := time "post for CanonicalStructuresFlatHOAS with big_flat-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; representation := HOAS |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for CanonicalStructuresHOAS with big-regression-quadratic") in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for CanonicalStructuresHOAS with big-regression-quadratic") in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for CanonicalStructuresHOAS with big-regression-quadratic") in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for CanonicalStructuresHOAS with big-regression-quadratic") in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for CanonicalStructuresHOAS with big-regression-quadratic") in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for CanonicalStructuresHOAS with big-regression-quadratic") in
       let restart_timer_postprocess := ltac:(restart_timer                 "postprocess for CanonicalStructuresHOAS with big-regression-quadratic") in
       let finish_timing_postprocess := ltac:(finish_timing ("Tactic call") "postprocess for CanonicalStructuresHOAS with big-regression-quadratic") in
       let time_intros_ tac          := time                                   "intros _ for CanonicalStructuresHOAS with big-regression-quadratic" tac in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for CanonicalStructuresHOAS with big-regression-quadratic" tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for CanonicalStructuresHOAS with big-regression-quadratic" tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy restart_timer_postprocess finish_timing_postprocess time_intros_ time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for CanonicalStructuresHOAS with big-regression-quadratic" do_cbv     x in
       let pre_reify  x := time  "pre for CanonicalStructuresHOAS with big-regression-quadratic" pre_reify  x in
       let do_reify   x := time "reif for CanonicalStructuresHOAS with big-regression-quadratic" do_reify   x in
       let post_reify x := time "post for CanonicalStructuresHOAS with big-regression-quadratic" post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | ?kind => fail 0 "Unrecognized kind:" kind
  end.

Ltac do_verify kind :=
  let is_flat := (eval cbv in kind.(is_flat)) in
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

for i, (is_flat, representation) in enumerate((is_flat, representation) for is_flat in ('true', 'false') for representation in ('HOAS', 'PHOAS')):
    kind = '{| is_flat := %s ; representation := %s |}' % (is_flat, representation)
    print(f'Ltac mkgoal{i} := mkgoal constr:({kind}).\nLtac time_solve_goal{i} := time_solve_goal constr:({kind}).\nLtac verify{i} := do_verify constr:({kind}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size {kind}) describe_goal mkgoal{i} redgoal ltac:(time_solve_goal{i} sz) verify{i} sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:({| is_flat := true ; representation := HOAS |}).
Ltac time_solve_goal0 := time_solve_goal constr:({| is_flat := true ; representation := HOAS |}).
Ltac verify0 := do_verify constr:({| is_flat := true ; representation := HOAS |}).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; representation := HOAS |}) describe_goal mkgoal0 redgoal ltac:(time_solve_goal0 sz) verify0 sz.

Ltac mkgoal1 := mkgoal constr:({| is_flat := true ; representation := PHOAS |}).
Ltac time_solve_goal1 := time_solve_goal constr:({| is_flat := true ; representation := PHOAS |}).
Ltac verify1 := do_verify constr:({| is_flat := true ; representation := PHOAS |}).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; representation := PHOAS |}) describe_goal mkgoal1 redgoal ltac:(time_solve_goal1 sz) verify1 sz.

Ltac mkgoal2 := mkgoal constr:({| is_flat := false ; representation := HOAS |}).
Ltac time_solve_goal2 := time_solve_goal constr:({| is_flat := false ; representation := HOAS |}).
Ltac verify2 := do_verify constr:({| is_flat := false ; representation := HOAS |}).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; representation := HOAS |}) describe_goal mkgoal2 redgoal ltac:(time_solve_goal2 sz) verify2 sz.

Ltac mkgoal3 := mkgoal constr:({| is_flat := false ; representation := PHOAS |}).
Ltac time_solve_goal3 := time_solve_goal constr:({| is_flat := false ; representation := PHOAS |}).
Ltac verify3 := do_verify constr:({| is_flat := false ; representation := PHOAS |}).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; representation := PHOAS |}) describe_goal mkgoal3 redgoal ltac:(time_solve_goal3 sz) verify3 sz.

Global Open Scope N_scope.

(*
Goal True.
  run3 Sanity.
*)
