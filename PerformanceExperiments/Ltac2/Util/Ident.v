Require Import Ltac2.Init.
Require Ltac2.Control.
Require Ltac2.Ident.
Require Import Ltac2Compat.Init.

Ltac2 rec find_error id xs :=
  match xs with
  | [] => None
  | x :: xs
    => let ((id', val)) := x in
       match Ident.equal id id' with
       | true => Some val
       | false => find_error id xs
       end
  end.
Ltac2 find id xs :=
  match find_error id xs with
  | None => Control.zero Not_found
  | Some val => val
  end.
