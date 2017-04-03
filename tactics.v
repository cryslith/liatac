Ltac unmatch :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
    let y := fresh in
    let Heq := fresh "Heq" in
    remember x as y eqn:Heq; destruct y; simpl; try rewrite <- Heq
  | [ _ : context[match ?x with _ => _ end] |- _ ] =>
    let y := fresh in
    let Heq := fresh "Heq" in
    remember x as y eqn:Heq; destruct y; simpl; try rewrite <- Heq
  end.

Ltac applyH :=
  multimatch goal with
    [ H : _ |- _ ] => apply H
  end.

Ltac eapplyH :=
  multimatch goal with
    [ H : _ |- _ ] => eapply H
  end.

Ltac rewriteH :=
  multimatch goal with
    [ H : _ = _ |- _ ] => rewrite H
  end.

Ltac require H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    assert H1 as x; [| specialize (H x)]
  end.
