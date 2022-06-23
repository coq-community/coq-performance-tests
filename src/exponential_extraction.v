Module Type T.
Parameter t : Type.
End T.

Module F (X:T).
  (* number of occurences determines the exponential: here 4 *)
  Definition t : Type := X.t * X.t * X.t * X.t.
End F.

Require Import Coq.extraction.Extraction.

Module A0. Definition t := nat. End A0.

Module A1 := F A0.
Module A2 := F A1.
Module A3 := F A2.
Module A4 := F A3.
Module A5 := F A4.
Module A6 := F A5.
Module A7 := F A6.
Module A8 := F A7.
Module A9 := F A8.

Set Boolean Equality Schemes.
Time Record Foo5 := { foo5 : A5.t }. (* 0.037s *)
Time Record Foo6 := { foo6 : A6.t }. (* 0.06 s *)
Time Record Foo7 := { foo7 : A7.t }. (* 0.248s *)
Time Record Foo8 := { foo8 : A8.t }. (* 1.015s *)
Time Record Foo9 := { foo9 : A9.t }. (* 3.811s *)

Time Redirect "A5" Recursive Extraction A5.t. (* 0.009s *)
Time Redirect "A6" Recursive Extraction A6.t. (* 0.041s *)
Time Redirect "A7" Recursive Extraction A7.t. (* 0.177s *)
Time Redirect "A8" Recursive Extraction A8.t. (* 0.744s *)
Time Redirect "A9" Recursive Extraction A9.t. (* 3.12 s *)
