Require Import Ltac2.Init.
Require Ltac2.Constr.
Require Ltac2.Array.
Require Import Ltac2Compat.Init.
Require Ltac2Compat.Constr.
Require Ltac2Compat.Array.

Ltac2 rec strip_casts term :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.Cast term' _ _ => strip_casts term'
  | _ => term
  end.

Module Unsafe.
  Ltac2 beta1 (c : constr) :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f args
      => match Constr.Unsafe.match_Lambda (Constr.Unsafe.kind f) with
         | Some l
           => let (id, f) := l in
              Constr.Unsafe.substnl (Array.to_list args) 0 f
         | _ => c
         end
    | _ => c
    end.
  Ltac2 zeta1 (c : constr) :=
    match Constr.Unsafe.match_LetIn (Constr.Unsafe.kind c) with
    | Some l
      => let (id, v, f) := l in
         Constr.Unsafe.substnl [v] 0 f
    | _ => c
    end.
End Unsafe.
