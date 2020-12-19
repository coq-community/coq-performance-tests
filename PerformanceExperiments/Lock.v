Definition key : unit. exact tt. Qed.
Definition lock {A} (v : A) : A := match key with tt => v end.
Lemma unlock {A} (v : A) : lock v = v.
Proof. unfold lock; destruct key; reflexivity. Qed.
