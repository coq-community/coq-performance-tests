Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Export PerformanceExperiments.rewrite_repeated_app_common.
Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import Ltac2.Control.
Require Ltac2.Notations.
Require Ltac2.Array.
Require Ltac2.Int.
Require PerformanceExperiments.Ltac2Compat.Array.
Require Import PerformanceExperiments.Ltac2Compat.Constr.

Module Import WithLtac2.
  Import Ltac2.Notations.
  (*Goal True.
    let x := Unsafe.make (Unsafe.mkLambda (Binder.make None 'True) (Unsafe.make (Unsafe.Rel 1))) in
    Message.print (Message.of_constr x).*)
  Ltac2 rec preshare_pf (f : constr) (g : constr) (f_res_ty : constr) (eq : constr) (eq_refl : constr) (cst : cast) (prop : constr) (hfg_ext : constr) (fx : constr) :=
    let mkRel i := Unsafe.make (Unsafe.Rel i) in
    match Unsafe.kind fx with
    | Unsafe.App _f args
      => let x := Array.get args 0 in
         let (under_lets_cont, gy) := preshare_pf f g f_res_ty eq eq_refl cst prop hfg_ext x in
         (* let x' := ... in let y' := ... in let pf' := ... in
            let fx' := f ^3 in let gy' := g ^3 in let pf' := hfg_ext ^5 ^4 ^3 in ... *)
         let fx'_bind := Binder.make None f_res_ty in
         let fx'_body := Unsafe.make (Unsafe.App f (Array.of_list [mkRel 3])) in
         let gy'_bind := Binder.make None f_res_ty in
         let gy'_body := Unsafe.make (Unsafe.App g (Array.of_list [mkRel 3])) in
         let pf'_bind := Binder.make
                           None
                           (Unsafe.make
                              (Unsafe.Cast
                                 (Unsafe.make
                                    (Unsafe.App
                                       eq
                                       (Array.of_list [f_res_ty; mkRel 2; mkRel 1])))
                                 cst
                                 prop)) in
         let pf'_body := Unsafe.make
                           (Unsafe.App
                              hfg_ext
                              (Array.of_list [mkRel 5; mkRel 4; mkRel 3])) in
         let gy := Unsafe.make (Unsafe.App g (Array.of_list [gy])) in
         ((fun k
           => under_lets_cont
                (fun v
                 => Unsafe.make
                      (Unsafe.mkLetIn
                         fx'_bind fx'_body
                         (Unsafe.make
                            (Unsafe.mkLetIn
                               gy'_bind gy'_body
                               (Unsafe.make
                                  (Unsafe.mkLetIn
                                     pf'_bind pf'_body
                                     (k v))))))))
          , gy)
    | _
      => let x := fx in
         (* let x' := fx in let y' := fx in let pf' := eq_refl fx in
            ... *)
         let fx'_bind := Binder.make None f_res_ty in
         let fx'_body := x in
         let gy'_bind := Binder.make None f_res_ty in
         let gy'_body := x in
         let pf'_bind := Binder.make
                           None
                           (Unsafe.make
                              (Unsafe.Cast
                                 (Unsafe.make
                                    (Unsafe.App
                                       eq
                                       (Array.of_list [f_res_ty; mkRel 2; mkRel 1])))
                                 cst
                                 prop)) in
         let pf'_body := Unsafe.make
                           (Unsafe.App
                              eq_refl
                              (Array.of_list [f_res_ty; x])) in
         ((fun k v
           => Unsafe.make
                (Unsafe.mkLetIn
                   fx'_bind fx'_body
                   (Unsafe.make
                      (Unsafe.mkLetIn
                         gy'_bind gy'_body
                         (Unsafe.make
                            (Unsafe.mkLetIn
                               pf'_bind pf'_body
                               (k v)))))))
          , x)
    end.

  Ltac2 get_normal_cast () :=
    match Unsafe.kind '(I : True) with
    | Unsafe.Cast _ cst _ => cst
    | _ => Control.throw Not_found
    end.

  Axiom admit : forall {T}, T.

  Ltac2 time_build_check_fast_proof (fx : constr) :=
    let mkRel i := Unsafe.make (Unsafe.Rel i) in
    let f := 'f in
    let g := 'g in
    let f_res_ty := 'nat in
    let eq := '(@eq) in
    let eq_refl := '(@eq_refl) in
    let hfg_ext := 'fg_ext in
    let c_I := 'I in
    let cst := get_normal_cast () in
    let c_admit := '(@admit) in
    let prop := 'Prop in
    let mkAdmit t := Unsafe.make (Unsafe.App c_admit (Array.of_list [t])) in
    let (mk, gy)
        := Control.time
             (Some "build-eval-thunk-regression-linear")
             (fun ()
              => let (mk, gy) := Control.time
                                   (Some "build-thunk-regression-linear")
                                   (fun () => preshare_pf f g f_res_ty eq eq_refl cst prop hfg_ext fx) in
                 (Control.time
                    (Some "eval-thunk-regression-linear")
                    (fun () => mk (fun c => c))
                  , gy)) in
    let let_I
        := Control.time
             (Some "build-I-regression-linear")
             (fun () => mk c_I) in
    let _
        := Control.time
             (Some "check-I-regression-linear")
             (fun () => Unsafe.check let_I) in
    let _
        := Control.time
             (Some "type-I-regression-linear")
             (fun () => Constr.type let_I) in
    let top_ty := Unsafe.make (Unsafe.App eq (Array.of_list [f_res_ty; fx; gy])) in
    let let_admit
        := Control.time
             (Some "build-admit-regression-linear")
             (fun () => mk (mkAdmit top_ty)) in
    let _
        := Control.time
             (Some "check-admit-regression-quadratic")
             (fun () => Unsafe.check let_admit) in
    let _
        := Control.time
             (Some "type-admit-regression-quadratic")
             (fun () => Constr.type let_admit) in
    (* fx = gy from context *)
    let under_ty := Unsafe.make (Unsafe.App eq (Array.of_list [f_res_ty; mkRel 3; mkRel 2])) in
    let let_admit_cast
        := Control.time
             (Some "build-admit-cast-regression-linear")
             (fun () => mk (Unsafe.make (Unsafe.Cast (mkAdmit under_ty) cst top_ty))) in
    let _
        := Control.time
             (Some "check-admit-cast-regression-quadratic")
             (fun () => Unsafe.check let_admit_cast) in
    let _
        := Control.time
             (Some "type-admit-cast-regression-quadratic")
             (fun () => Constr.type let_admit_cast) in
    let let_pf_cast
        := Control.time
             (Some "build-pf-cast-regression-linear")
             (fun () => mk (Unsafe.make (Unsafe.Cast (mkRel 1) cst top_ty))) in
    let _
        := Control.time
             (Some "check-pf-cast-regression-quadratic")
             (fun () => Unsafe.check let_pf_cast) in
    let _
        := Control.time
             (Some "type-pf-cast-regression-quadratic")
             (fun () => Constr.type let_pf_cast) in
    let_pf_cast.

  Ltac2 fast_rewrite () :=
    let fx := (lazy_match! goal with
              | [ |- ?fx = _ ] => fx
               end) in
    let pf := time_build_check_fast_proof fx in
    Control.time
      (Some "refine-regression-quadratic-regression-linear")
      (fun () => Control.refine (fun () => pf)).

End WithLtac2.

Ltac fast_rewrite_ltac2 :=
  ltac2:(fast_rewrite ()).
Global Set Default Proof Mode "Classic".
