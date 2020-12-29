(** * Reification by Ltac2, copying Ltac1 *)

Require Import Reify.ReifyCommon.
Require Ltac2.Ltac2.
Require Ltac2.Ltac1.
Require Ltac2.Option.
Import Ltac2.Init.
Import Ltac2.Notations.
Require Ltac2Compat.Ltac2.
Import Ltac2Compat.Init.
Require PerformanceExperiments.Ltac2.Util.Constr.
Require PerformanceExperiments.Ltac2.Util.Ident.

Module Ltac2.
  (** This file contains the Ltac2 version of Ltac1 reification, from
      [LtacTacInTermExplicitCtx.v]. *)

  Ltac2 rec reify_helper
        (var : constr)
        (term : constr)
        (ctx : (ident * ident) list)
    :=
      let reify_rec term := reify_helper var term ctx in
      Control.plus
        (fun ()
         => match Constr.Unsafe.kind (Constr.strip_casts term) with
            | Constr.Unsafe.Var x
              => let v := Ident.find x ctx in
                 let v := Constr.Unsafe.make (Constr.Unsafe.Var v) in
                 constr:(@Var $var $v)
            | _ => Control.zero Not_found
            end)
        (fun _
         => (lazy_match! term with
            | 0 => constr:(@NatO $var)
            | S ?x
              => let rx := reify_rec x in
                 constr:(@NatS $var $rx)
            | ?x * ?y
              => let rx := reify_rec x in
                 let ry := reify_rec y in
                 constr:(@NatMul $var $rx $ry)
            | (dlet x := ?v in @?f x)
              => let rv := reify_rec v in

                 (** We assume the invariant that all bound variables
                     show up as [Rel] nodes rather than [Var] nodes *)

                 match Constr.Unsafe.match_Lambda (Constr.Unsafe.kind f) with
                 | Some l
                   => let (binder, c) := l in
                      let id := Constr.Binder.name binder in
                      let t := Constr.Binder.type binder in
                      let c_set := Fresh.Free.of_ids
                                     (List.map (fun (id, _, _) => id)
                                               (Control.hyps ())) in
                      let c_set := Fresh.Free.union
                                     c_set
                                     (Fresh.Free.of_constr c) in
                      let x_base := match id with
                                    | Some id => id
                                    | None => @x
                                    end in
                      let x := Fresh.fresh c_set x_base in
                      let c_set := Fresh.Free.union
                                     c_set
                                     (Fresh.Free.of_ids [x]) in
                      let not_x := Fresh.fresh c_set x_base in
                      let ctx := (x, not_x) :: ctx in
                      let c := Constr.Unsafe.substnl
                                 [Constr.Unsafe.make (Constr.Unsafe.Var x)]
                                 0
                                 c in
                      let ret :=
                          Constr.in_context
                            x t
                            (fun ()
                             => let rf :=
                                    Constr.in_context
                                      not_x var
                                      (fun ()
                                       => let rf := reify_helper var c ctx in
                                          Control.refine (fun () => rf)) in
                                Control.refine (fun () => rf)) in
                      (lazy_match! ret with
                      | fun _ => ?rf
                        => constr:(@LetIn $var $rv $rf)
                      | ?f
                        => let msg :=
                               Message.concat
                                 (Message.of_string
                                    "Failed to eliminate functional dependencies in ")
                                 (Message.of_constr f) in
                           Message.print msg;
                      Control.zero
                        (Tactic_failure (Some msg))
                       end)
                 | _ => let msg :=
                            Message.concat
                              (Message.of_string "Bad let-in function: ")
                              (Message.of_constr f) in
                        Message.print msg;
            Control.zero (Tactic_failure (Some msg))
             end
            | _
              => let msg := Message.concat
                              (Message.of_string "Unrecognized term: ")
                              (Message.of_constr term) in
                 Message.print msg;
            Control.zero (Tactic_failure (Some msg))
             end)).

  Ltac2 reify (var : constr) (term : constr) := reify_helper var term [].

  Ltac reify var term :=
    let ret :=
        constr:(ltac:(let f := ltac2:(var term |-
                                      let var := Option.get (Ltac1.to_constr var) in
                                      let term := Option.get (Ltac1.to_constr term) in
                                      let rv := reify var term in
                                      Control.refine (fun () => rv)) in
                      f constr:(var) constr:(term))) in
    ret.

  Ltac Reify x := Reify_of reify x.
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
      Reify Denote ().
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
End Ltac2.

Module Ltac2LowLevel.
  (** * Reification by Ltac2, using unsafe low-level primitives *)

  (** This function is parameterized over the constants which we are
      reifying ([gO], [gS], [gNatMul], [gLetIn]) and over Ltac2
      functions that build applications of the reified versions of
      these functions to reified arguments. *)
  Ltac2 rec unsafe_reify_helper
        (mkVar : constr -> 'a)
        (mkO : 'a)
        (mkS : 'a -> 'a)
        (mkNatMul : 'a -> 'a -> 'a)
        (mkLetIn : 'a -> binder -> 'a -> 'a)
        (gO : constr)
        (gS : constr)
        (gNatMul : constr)
        (gLetIn : constr)
        (unrecognized : constr -> 'a)
        (term : constr)
    :=
      let reify_rec term :=
          unsafe_reify_helper
            mkVar mkO mkS mkNatMul mkLetIn gO gS gNatMul gLetIn unrecognized term in
      let kterm := Constr.Unsafe.kind term in
      match Constr.equal term gO with
      | true
        => mkO
      | false
        =>
        match kterm with
        | Constr.Unsafe.Rel _ => mkVar term
        | Constr.Unsafe.Var _ => mkVar term
        | Constr.Unsafe.Cast term _ _ => reify_rec term
        | Constr.Unsafe.App f args
          =>
          match Constr.equal f gS with
          | true
            => let x := Array.get args 0 in
               let rx := reify_rec x in
               mkS rx
          | false
            =>
            match Constr.equal f gNatMul with
            | true
              => let x := Array.get args 0 in
                 let y := Array.get args 1 in
                 let rx := reify_rec x in
                 let ry := reify_rec y in
                 mkNatMul rx ry
            | false
              =>
              match Constr.equal f gLetIn with
              | true
                => let x := Array.get args 2 (* assume the first two args are type params *) in
                   let f := Array.get args 3 in
                   match Constr.Unsafe.match_Lambda (Constr.Unsafe.kind f) with
                   | Some l
                     => let (binder, body) := l in
                        let rx := reify_rec x in
                        let rf := reify_rec body in
                        mkLetIn rx binder rf
                   | _ => unrecognized term
                   end
              | false
                => unrecognized term
              end
            end
          end
        | _
          => unrecognized term
        end
      end.

  Ltac2 unsafe_reify (var_Type : constr) (var : constr) (term : constr) :=
    let cst := Constr.get_default_cast () in
    let var_casted (* work around COQBUG(https://github.com/coq/coq/issues/12601) *)
        := Constr.Unsafe.make (Constr.Unsafe.Cast var cst var_Type) in
    let cVar := '@Var in
    let cO := '@NatO in
    let cS := '@NatS in
    let cNatMul := '@NatMul in
    let cLetIn := '@LetIn in
    let gO := 'O in
    let gS := 'S in
    let gNatMul := '@Nat.mul in
    let gLetIn := '@Let_In in
    let mk0VarArgs :=
        let args := Array.make 1 var in
        args in
    let mk1VarArgs (x : constr) :=
        let args := Array.make 2 var in
        let () := Array.set args 1 x in
        args in
    let mk2VarArgs (x : constr) (y : constr) :=
        let args := Array.make 3 var in
        let () := Array.set args 1 x in
        let () := Array.set args 2 y in
        args in
    let mkApp0 (f : constr) :=
        Constr.Unsafe.make (Constr.Unsafe.App f mk0VarArgs) in
    let mkApp1 (f : constr) (x : constr) :=
        Constr.Unsafe.make (Constr.Unsafe.App f (mk1VarArgs x)) in
    let mkApp2 (f : constr) (x : constr) (y : constr) :=
        Constr.Unsafe.make (Constr.Unsafe.App f (mk2VarArgs x y)) in
    let mkVar (v : constr) := mkApp1 cVar v in
    let mkO := mkApp0 cO in
    let mkS (v : constr) := mkApp1 cS v in
    let mkNatMul (x : constr) (y : constr) := mkApp2 cNatMul x y in
    let mkcLetIn (x : constr) (y : constr) := mkApp2 cLetIn x y in
    let mkLetIn (x : constr) (bindx : binder) (fbody : constr)
        := mkcLetIn x (Constr.Unsafe.make (Constr.Unsafe.mkLambda (Constr.Binder.make (Constr.Binder.name bindx) var_casted) fbody)) in
    let ret := unsafe_reify_helper
                 mkVar mkO mkS mkNatMul mkLetIn gO gS gNatMul gLetIn
                 (fun term => term)
                 term in
    ret.
  Ltac2 check_result (ret : constr) :=
    match Constr.Unsafe.check ret with
    | Val rterm => rterm
    | Err exn => (Message.print (Message.concat (Message.of_string "Invalid constr in check_result:") (Message.of_constr ret));
                 Control.zero exn)
    end.
  Ltac2 reify (var : constr) (term : constr) :=
    check_result (unsafe_reify (Constr.type var) var term).

  Ltac2 unsafe_Reify (term : constr) :=
    let fresh_set := Fresh.Free.of_constr term in
    let idvar := Fresh.fresh fresh_set @var in
    let var := Constr.Unsafe.make (Constr.Unsafe.Var idvar) in
    let cType := 'Type in
    let rterm := unsafe_reify cType var term in
    let rterm := Constr.Unsafe.closenl [idvar] 1 rterm in
    Constr.Unsafe.make (Constr.Unsafe.mkLambda (Constr.Binder.make (Some idvar) cType) rterm).

  Ltac2 do_Reify (term : constr) :=
    check_result (unsafe_Reify term).

  Ltac unsafe_reify var term :=
    let ret :=
        constr:(ltac:(let f := ltac2:(var term |-
                                      let var := Option.get (Ltac1.to_constr var) in
                                      let term := Option.get (Ltac1.to_constr term) in
                                      let var_Type := Constr.type var in
                                      let rv := unsafe_reify var_Type var term in
                                      Control.refine (fun () => rv)) in
                      f constr:(var) constr:(term))) in
    ret.
  Ltac reify var term :=
    let ret :=
        constr:(ltac:(let f := ltac2:(var term |-
                                      let var := Option.get (Ltac1.to_constr var) in
                                      let term := Option.get (Ltac1.to_constr term) in
                                      let rv := reify var term in
                                      Control.refine (fun () => rv)) in
                      f constr:(var) constr:(term))) in
    ret.
  Ltac unsafe_Reify term :=
    let ret :=
        constr:(ltac:(let f := ltac2:(term |-
                                      let term := Option.get (Ltac1.to_constr term) in
                                      let rv := unsafe_Reify term in
                                      Control.refine (fun () => rv)) in
                      f constr:(term))) in
    ret.
  Ltac Reify term :=
    let ret :=
        constr:(ltac:(let f := ltac2:(term |-
                                      let term := Option.get (Ltac1.to_constr term) in
                                      let rv := do_Reify term in
                                      Control.refine (fun () => rv)) in
                      f constr:(term))) in
    ret.

  Ltac do_unsafe_Reify_rhs
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
      unsafe_Reify Denote ().
  Ltac post_unsafe_Reify_rhs do_trans _ := ReifyCommon.post_Reify_rhs do_trans ().
  Ltac unsafe_Reify_rhs
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
      unsafe_Reify ().

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
      Reify Denote ().
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
End Ltac2LowLevel.
