(** * Ltac-based reification, using uncurrying to reucurse under binders *)
Require Import Coq.NArith.NArith.
Require Import PerformanceExperiments.Harness.
Require Import Reify.BenchmarkExtraUtil.
Require
  Reify.LtacPrimUncurry
  Reify.LtacTCPrimPair Reify.LtacTCGallinaCtx Reify.LtacTCExplicitCtx
  Reify.LtacTacInTermPrimPair Reify.LtacTacInTermGallinaCtx Reify.LtacTacInTermExplicitCtx.

Export
  LtacTCExplicitCtx.Exports
  LtacTCGallinaCtx.Exports
  LtacTCPrimPair.Exports
.

Inductive reif_kind := LtacPrimUncurry | LtacTCPrimPair | LtacTCGallinaCtx | LtacTCExplicitCtx | LtacTacInTermPrimPair | LtacTacInTermGallinaCtx | LtacTacInTermExplicitCtx.
Record kind := { is_flat : bool ; ltac_kind : reif_kind }.

Definition args_of_size (k : kind) (s : size) : list N
  := match k.(ltac_kind), k.(is_flat), s with
     | _, _, Sanity => List.firstn 4 sequence
     | LtacPrimUncurry, true , SuperFast => args_of_max_n   400
     | LtacPrimUncurry, true , Fast      => args_of_max_n  6000
     | LtacPrimUncurry, true , Medium    => args_of_max_n 30000
     | LtacPrimUncurry, false, SuperFast => args_of_max_n    85
     | LtacPrimUncurry, false, Fast      => args_of_max_n   175
     | LtacPrimUncurry, false, Medium    => args_of_max_n   700

     | _              , true , SuperFast => args_of_max_n   400
     | _              , true , Fast      => args_of_max_n  6000
     | _              , true , Medium    => args_of_max_n 30000
     | _              , false, SuperFast => args_of_max_n   100
     | _              , false, Fast      => args_of_max_n   300
     | _              , false, Medium    => args_of_max_n  2000

     | _              , _    , _         => args_of_max_n 30000
     end.

Ltac mkgoal kind := let is_flat := (eval cbv in kind.(is_flat)) in BenchmarkExtraUtil.mkgoal is_flat (* n *).
Ltac redgoal _ := idtac.
Ltac describe_goal n := idtac "Params: n=" n.
Ltac time_solve_goal kind sz :=
  let kind := (eval cbv in kind) in
  let is_flat := (eval cbv in kind.(is_flat)) in
  let ltac_kind := (eval cbv in kind.(ltac_kind)) in
  let do_cbv := BenchmarkExtraUtil.do_cbv in
  let do_trans := (eval lazy in (do_trans_of_size sz)) in
  let pre_reify := BenchmarkExtraUtil.noop in
  let do_reify := lazymatch ltac_kind with
                  | LtacPrimUncurry => LtacPrimUncurry.do_Reify_rhs do_trans
                  | LtacTCPrimPair => LtacTCPrimPair.do_Reify_rhs do_trans
                  | LtacTCGallinaCtx => LtacTCGallinaCtx.do_Reify_rhs do_trans
                  | LtacTCExplicitCtx => LtacTCExplicitCtx.do_Reify_rhs do_trans
                  | LtacTacInTermPrimPair => LtacTacInTermPrimPair.do_Reify_rhs do_trans
                  | LtacTacInTermGallinaCtx => LtacTacInTermGallinaCtx.do_Reify_rhs do_trans
                  | LtacTacInTermExplicitCtx => LtacTacInTermExplicitCtx.do_Reify_rhs do_trans
                  end in
  let post_reify := lazymatch ltac_kind with
                    | LtacPrimUncurry => LtacPrimUncurry.post_Reify_rhs do_trans
                    | LtacTCPrimPair => LtacTCPrimPair.post_Reify_rhs do_trans
                    | LtacTCGallinaCtx => LtacTCGallinaCtx.post_Reify_rhs do_trans
                    | LtacTCExplicitCtx => LtacTCExplicitCtx.post_Reify_rhs do_trans
                    | LtacTacInTermPrimPair => LtacTacInTermPrimPair.post_Reify_rhs do_trans
                    | LtacTacInTermGallinaCtx => LtacTacInTermGallinaCtx.post_Reify_rhs do_trans
                    | LtacTacInTermExplicitCtx => LtacTacInTermExplicitCtx.post_Reify_rhs do_trans
                    end in
  lazymatch kind with
  | {| is_flat := true ; ltac_kind := LtacPrimUncurry |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacPrimUncurry with big_flat"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacPrimUncurry with big_flat"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacPrimUncurry with big_flat"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacPrimUncurry with big_flat"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacPrimUncurry with big_flat"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacPrimUncurry with big_flat"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacPrimUncurry with big_flat"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacPrimUncurry with big_flat"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacPrimUncurry with big_flat"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacPrimUncurry with big_flat"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacPrimUncurry with big_flat"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacPrimUncurry with big_flat"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; ltac_kind := LtacTCPrimPair |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTCPrimPair with big_flat"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTCPrimPair with big_flat"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTCPrimPair with big_flat"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTCPrimPair with big_flat"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTCPrimPair with big_flat"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTCPrimPair with big_flat"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTCPrimPair with big_flat"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTCPrimPair with big_flat"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTCPrimPair with big_flat"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTCPrimPair with big_flat"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTCPrimPair with big_flat"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTCPrimPair with big_flat"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; ltac_kind := LtacTCGallinaCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTCGallinaCtx with big_flat"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; ltac_kind := LtacTCExplicitCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTCExplicitCtx with big_flat"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; ltac_kind := LtacTacInTermPrimPair |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTacInTermPrimPair with big_flat"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; ltac_kind := LtacTacInTermGallinaCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTacInTermGallinaCtx with big_flat"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := true ; ltac_kind := LtacTacInTermExplicitCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTacInTermExplicitCtx with big_flat"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; ltac_kind := LtacPrimUncurry |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacPrimUncurry with big"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacPrimUncurry with big"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacPrimUncurry with big"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacPrimUncurry with big"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacPrimUncurry with big"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacPrimUncurry with big"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacPrimUncurry with big"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacPrimUncurry with big"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacPrimUncurry with big"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacPrimUncurry with big"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacPrimUncurry with big"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacPrimUncurry with big"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; ltac_kind := LtacTCPrimPair |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTCPrimPair with big"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTCPrimPair with big"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTCPrimPair with big"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTCPrimPair with big"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTCPrimPair with big"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTCPrimPair with big"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTCPrimPair with big"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTCPrimPair with big"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTCPrimPair with big"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTCPrimPair with big"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTCPrimPair with big"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTCPrimPair with big"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; ltac_kind := LtacTCGallinaCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTCGallinaCtx with big"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTCGallinaCtx with big"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTCGallinaCtx with big"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTCGallinaCtx with big"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTCGallinaCtx with big"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTCGallinaCtx with big"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTCGallinaCtx with big"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTCGallinaCtx with big"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTCGallinaCtx with big"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTCGallinaCtx with big"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTCGallinaCtx with big"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTCGallinaCtx with big"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; ltac_kind := LtacTCExplicitCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTCExplicitCtx with big"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTCExplicitCtx with big"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTCExplicitCtx with big"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTCExplicitCtx with big"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTCExplicitCtx with big"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTCExplicitCtx with big"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTCExplicitCtx with big"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTCExplicitCtx with big"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTCExplicitCtx with big"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTCExplicitCtx with big"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTCExplicitCtx with big"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTCExplicitCtx with big"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; ltac_kind := LtacTacInTermPrimPair |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTacInTermPrimPair with big"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTacInTermPrimPair with big"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTacInTermPrimPair with big"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTacInTermPrimPair with big"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTacInTermPrimPair with big"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTacInTermPrimPair with big"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTacInTermPrimPair with big"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTacInTermPrimPair with big"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTacInTermPrimPair with big"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTacInTermPrimPair with big"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTacInTermPrimPair with big"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTacInTermPrimPair with big"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; ltac_kind := LtacTacInTermGallinaCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTacInTermGallinaCtx with big"(*-regression-quadratic*) post_reify x in
       BenchmarkExtraUtil.time_solve_goal do_cbv pre_reify do_reify post_reify
  | {| is_flat := false ; ltac_kind := LtacTacInTermExplicitCtx |}
    => let restart_timer_norm_reif   := ltac:(restart_timer                   "norm reif for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*)) in
       let finish_timing_norm_reif   := ltac:(finish_timing ("Tactic call")   "norm reif for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*)) in
       let restart_timer_actual_reif := ltac:(restart_timer                 "actual reif for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*)) in
       let finish_timing_actual_reif := ltac:(finish_timing ("Tactic call") "actual reif for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*)) in
       let restart_timer_eval_lazy   := ltac:(restart_timer                   "eval lazy for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*)) in
       let finish_timing_eval_lazy   := ltac:(finish_timing ("Tactic call")   "eval lazy for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*)) in
       let time_lazy_beta_iota tac   := time                             "lazy beta iota for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*) tac in
       let time_transitivity_Denote_rv tac := time             "transitivity (Denote rv) for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*) tac in
       let do_reify := do_reify restart_timer_norm_reif finish_timing_norm_reif restart_timer_actual_reif finish_timing_actual_reif restart_timer_eval_lazy finish_timing_eval_lazy time_lazy_beta_iota time_transitivity_Denote_rv in
       let do_cbv     x := time  "cbv for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*) do_cbv     x in
       let pre_reify  x := time  "pre for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*) pre_reify  x in
       let do_reify   x := time "reif for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*) do_reify   x in
       let post_reify x := time "post for LtacTacInTermExplicitCtx with big"(*-regression-quadratic*) post_reify x in
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

for i, (is_flat, ltac_kind) in enumerate((is_flat, ltac_kind) for is_flat in ('true', 'false') for ltac_kind in ('LtacPrimUncurry', 'LtacTCPrimPair', 'LtacTCGallinaCtx', 'LtacTCExplicitCtx', 'LtacTacInTermPrimPair', 'LtacTacInTermGallinaCtx', 'LtacTacInTermExplicitCtx')):
    kind = '{| is_flat := %s ; ltac_kind := %s |}' % (is_flat, ltac_kind)
    print(f'Ltac mkgoal{i} := mkgoal constr:({kind}).\nLtac time_solve_goal{i} := time_solve_goal constr:({kind}).\nLtac verify{i} := do_verify constr:({kind}).\nLtac run{i} sz := Harness.runtests_verify_sanity (args_of_size {kind}) describe_goal mkgoal{i} redgoal ltac:(time_solve_goal{i} sz) verify{i} sz.\n')

>>>
 *)
Ltac mkgoal0 := mkgoal constr:({| is_flat := true ; ltac_kind := LtacPrimUncurry |}).
Ltac time_solve_goal0 := time_solve_goal constr:({| is_flat := true ; ltac_kind := LtacPrimUncurry |}).
Ltac verify0 := do_verify constr:({| is_flat := true ; ltac_kind := LtacPrimUncurry |}).
Ltac run0 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; ltac_kind := LtacPrimUncurry |}) describe_goal mkgoal0 redgoal ltac:(time_solve_goal0 sz) verify0 sz.

Ltac mkgoal1 := mkgoal constr:({| is_flat := true ; ltac_kind := LtacTCPrimPair |}).
Ltac time_solve_goal1 := time_solve_goal constr:({| is_flat := true ; ltac_kind := LtacTCPrimPair |}).
Ltac verify1 := do_verify constr:({| is_flat := true ; ltac_kind := LtacTCPrimPair |}).
Ltac run1 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; ltac_kind := LtacTCPrimPair |}) describe_goal mkgoal1 redgoal ltac:(time_solve_goal1 sz) verify1 sz.

Ltac mkgoal2 := mkgoal constr:({| is_flat := true ; ltac_kind := LtacTCGallinaCtx |}).
Ltac time_solve_goal2 := time_solve_goal constr:({| is_flat := true ; ltac_kind := LtacTCGallinaCtx |}).
Ltac verify2 := do_verify constr:({| is_flat := true ; ltac_kind := LtacTCGallinaCtx |}).
Ltac run2 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; ltac_kind := LtacTCGallinaCtx |}) describe_goal mkgoal2 redgoal ltac:(time_solve_goal2 sz) verify2 sz.

Ltac mkgoal3 := mkgoal constr:({| is_flat := true ; ltac_kind := LtacTCExplicitCtx |}).
Ltac time_solve_goal3 := time_solve_goal constr:({| is_flat := true ; ltac_kind := LtacTCExplicitCtx |}).
Ltac verify3 := do_verify constr:({| is_flat := true ; ltac_kind := LtacTCExplicitCtx |}).
Ltac run3 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; ltac_kind := LtacTCExplicitCtx |}) describe_goal mkgoal3 redgoal ltac:(time_solve_goal3 sz) verify3 sz.

Ltac mkgoal4 := mkgoal constr:({| is_flat := true ; ltac_kind := LtacTacInTermPrimPair |}).
Ltac time_solve_goal4 := time_solve_goal constr:({| is_flat := true ; ltac_kind := LtacTacInTermPrimPair |}).
Ltac verify4 := do_verify constr:({| is_flat := true ; ltac_kind := LtacTacInTermPrimPair |}).
Ltac run4 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; ltac_kind := LtacTacInTermPrimPair |}) describe_goal mkgoal4 redgoal ltac:(time_solve_goal4 sz) verify4 sz.

Ltac mkgoal5 := mkgoal constr:({| is_flat := true ; ltac_kind := LtacTacInTermGallinaCtx |}).
Ltac time_solve_goal5 := time_solve_goal constr:({| is_flat := true ; ltac_kind := LtacTacInTermGallinaCtx |}).
Ltac verify5 := do_verify constr:({| is_flat := true ; ltac_kind := LtacTacInTermGallinaCtx |}).
Ltac run5 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; ltac_kind := LtacTacInTermGallinaCtx |}) describe_goal mkgoal5 redgoal ltac:(time_solve_goal5 sz) verify5 sz.

Ltac mkgoal6 := mkgoal constr:({| is_flat := true ; ltac_kind := LtacTacInTermExplicitCtx |}).
Ltac time_solve_goal6 := time_solve_goal constr:({| is_flat := true ; ltac_kind := LtacTacInTermExplicitCtx |}).
Ltac verify6 := do_verify constr:({| is_flat := true ; ltac_kind := LtacTacInTermExplicitCtx |}).
Ltac run6 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := true ; ltac_kind := LtacTacInTermExplicitCtx |}) describe_goal mkgoal6 redgoal ltac:(time_solve_goal6 sz) verify6 sz.

Ltac mkgoal7 := mkgoal constr:({| is_flat := false ; ltac_kind := LtacPrimUncurry |}).
Ltac time_solve_goal7 := time_solve_goal constr:({| is_flat := false ; ltac_kind := LtacPrimUncurry |}).
Ltac verify7 := do_verify constr:({| is_flat := false ; ltac_kind := LtacPrimUncurry |}).
Ltac run7 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; ltac_kind := LtacPrimUncurry |}) describe_goal mkgoal7 redgoal ltac:(time_solve_goal7 sz) verify7 sz.

Ltac mkgoal8 := mkgoal constr:({| is_flat := false ; ltac_kind := LtacTCPrimPair |}).
Ltac time_solve_goal8 := time_solve_goal constr:({| is_flat := false ; ltac_kind := LtacTCPrimPair |}).
Ltac verify8 := do_verify constr:({| is_flat := false ; ltac_kind := LtacTCPrimPair |}).
Ltac run8 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; ltac_kind := LtacTCPrimPair |}) describe_goal mkgoal8 redgoal ltac:(time_solve_goal8 sz) verify8 sz.

Ltac mkgoal9 := mkgoal constr:({| is_flat := false ; ltac_kind := LtacTCGallinaCtx |}).
Ltac time_solve_goal9 := time_solve_goal constr:({| is_flat := false ; ltac_kind := LtacTCGallinaCtx |}).
Ltac verify9 := do_verify constr:({| is_flat := false ; ltac_kind := LtacTCGallinaCtx |}).
Ltac run9 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; ltac_kind := LtacTCGallinaCtx |}) describe_goal mkgoal9 redgoal ltac:(time_solve_goal9 sz) verify9 sz.

Ltac mkgoal10 := mkgoal constr:({| is_flat := false ; ltac_kind := LtacTCExplicitCtx |}).
Ltac time_solve_goal10 := time_solve_goal constr:({| is_flat := false ; ltac_kind := LtacTCExplicitCtx |}).
Ltac verify10 := do_verify constr:({| is_flat := false ; ltac_kind := LtacTCExplicitCtx |}).
Ltac run10 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; ltac_kind := LtacTCExplicitCtx |}) describe_goal mkgoal10 redgoal ltac:(time_solve_goal10 sz) verify10 sz.

Ltac mkgoal11 := mkgoal constr:({| is_flat := false ; ltac_kind := LtacTacInTermPrimPair |}).
Ltac time_solve_goal11 := time_solve_goal constr:({| is_flat := false ; ltac_kind := LtacTacInTermPrimPair |}).
Ltac verify11 := do_verify constr:({| is_flat := false ; ltac_kind := LtacTacInTermPrimPair |}).
Ltac run11 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; ltac_kind := LtacTacInTermPrimPair |}) describe_goal mkgoal11 redgoal ltac:(time_solve_goal11 sz) verify11 sz.

Ltac mkgoal12 := mkgoal constr:({| is_flat := false ; ltac_kind := LtacTacInTermGallinaCtx |}).
Ltac time_solve_goal12 := time_solve_goal constr:({| is_flat := false ; ltac_kind := LtacTacInTermGallinaCtx |}).
Ltac verify12 := do_verify constr:({| is_flat := false ; ltac_kind := LtacTacInTermGallinaCtx |}).
Ltac run12 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; ltac_kind := LtacTacInTermGallinaCtx |}) describe_goal mkgoal12 redgoal ltac:(time_solve_goal12 sz) verify12 sz.

Ltac mkgoal13 := mkgoal constr:({| is_flat := false ; ltac_kind := LtacTacInTermExplicitCtx |}).
Ltac time_solve_goal13 := time_solve_goal constr:({| is_flat := false ; ltac_kind := LtacTacInTermExplicitCtx |}).
Ltac verify13 := do_verify constr:({| is_flat := false ; ltac_kind := LtacTacInTermExplicitCtx |}).
Ltac run13 sz := Harness.runtests_verify_sanity (args_of_size {| is_flat := false ; ltac_kind := LtacTacInTermExplicitCtx |}) describe_goal mkgoal13 redgoal ltac:(time_solve_goal13 sz) verify13 sz.

Global Open Scope N_scope.

(*
Goal True.
  run0 Sanity.
  run1 Sanity.
  run2 Sanity.
  run3 Sanity.
  run4 Sanity.
  run5 Sanity.
  run6 Sanity.
  run7 Sanity.
  run8 Sanity.
  run9 Sanity.
  run10 Sanity.
  run11 Sanity.
  run12 Sanity.
  run13 Sanity.
*)
