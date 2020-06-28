Axiom admit : forall {T}, T.

Ltac time_abstract_gen time_abstract_tac close_abstract_restart_timer close_abstract_finish_timing tac :=
  cut True;
  [ intros _;
    time_abstract_tac
      ltac:(fun _
            => abstract (
                   cut True;
                   [ intros _;
                     tac ();
                     exact admit
                   | close_abstract_restart_timer ();
                     exact I ]))
  | close_abstract_finish_timing ();
    exact I ].
Tactic Notation "time_abstract_gen" tactic0(time_abstract_tac) tactic0(close_abstract_restart_timer) tactic0(close_abstract_finish_timing) tactic0(tac) :=
  time_abstract_gen time_abstract_tac ltac:(fun _ => close_abstract_restart_timer) ltac:(fun _ => close_abstract_finish_timing) ltac:(fun _ => tac).

Ltac default_time_abstract_tac tac := time "abstract" (tac ()).
Ltac default_close_abstract_restart_timer := restart_timer.
Ltac default_close_abstract_finish_timing := finish_timing ( "Tactic call close-abstract" ).

Ltac time_abstract tac :=
  time_abstract_gen default_time_abstract_tac default_close_abstract_restart_timer default_close_abstract_finish_timing tac.

Tactic Notation "time_abstract" tactic3(tac) :=
  time_abstract tac.

Inductive regression_kind :=
| regression_exponential
| regression_factorial
| regression_linear
| regression_quadratic
| regression_cubic
| regression_quartic
| regression_quintic.

Ltac default_time_abstract_regression_gen_tac rk
  := lazymatch rk with
     | regression_exponential => fun tac => time "abstract-regression-exponential" (tac ())
     | regression_factorial => fun tac => time "abstract-regression-factorial" (tac ())
     | regression_linear => fun tac => time "abstract-regression-linear" (tac ())
     | regression_quadratic => fun tac => time "abstract-regression-quadratic" (tac ())
     | regression_cubic => fun tac => time "abstract-regression-cubic" (tac ())
     | regression_quartic => fun tac => time "abstract-regression-quartic" (tac ())
     | regression_quintic => fun tac => time "abstract-regression-quintic" (tac ())
     end.
Ltac default_close_abstract_regression_gen_finish_timing rk :=
  lazymatch rk with
  | regression_exponential => fun _ => finish_timing ( "Tactic call close-abstract-regression-exponential" )
  | regression_factorial => fun _ => finish_timing ( "Tactic call close-abstract-regression-factorial" )
  | regression_linear => fun _ => finish_timing ( "Tactic call close-abstract-regression-linear" )
  | regression_quadratic => fun _ => finish_timing ( "Tactic call close-abstract-regression-quadratic" )
  | regression_cubic => fun _ => finish_timing ( "Tactic call close-abstract-regression-cubic" )
  | regression_quartic => fun _ => finish_timing ( "Tactic call close-abstract-regression-quartic" )
  | regression_quintic => fun _ => finish_timing ( "Tactic call close-abstract-regression-quintic" )
  end.

Ltac time_abstract_regression_gen rk :=
  let time_abstract_tac := default_time_abstract_regression_gen_tac rk in
  let close_abstract := default_close_abstract_regression_gen_finish_timing rk in
  fun tac
  => time_abstract_gen time_abstract_tac default_close_abstract_restart_timer (close_abstract ()) tac.

Tactic Notation "time_abstract_regression_exponential" tactic3(tac) := time_abstract_regression_gen regression_exponential tac.
Tactic Notation "time_abstract_regression_factorial" tactic3(tac) := time_abstract_regression_gen regression_factorial tac.
Tactic Notation "time_abstract_regression_linear" tactic3(tac) := time_abstract_regression_gen regression_linear tac.
Tactic Notation "time_abstract_regression_quadratic" tactic3(tac) := time_abstract_regression_gen regression_quadratic tac.
Tactic Notation "time_abstract_regression_cubic" tactic3(tac) := time_abstract_regression_gen regression_cubic tac.
Tactic Notation "time_abstract_regression_quartic" tactic3(tac) := time_abstract_regression_gen regression_quartic tac.
Tactic Notation "time_abstract_regression_quintic" tactic3(tac) := time_abstract_regression_gen regression_quintic tac.
