(** We test memory usage of typeclass resification of let-binders to PHOAS *)
Require Import CoqPerformanceTests.typeclass_reification_common.

Time Definition foo10 : goal 10. Time solve_P. Time Qed.
Time Definition foo50 : goal 50. Time solve_P. Time Qed.
Time Definition foo100 : goal 100. Time solve_P. Time Qed.
Time Definition foo150 : goal 150. Time solve_P. Time Qed.
Time Definition foo200 : goal 200. Time solve_P. Time Qed.
