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

Example test_unmatch : forall x, match x with
                                 | true => true
                                 | false => true
                                 end = true.
Proof.
  intros; unmatch; reflexivity.
Qed.

Ltac multiH tac :=
  multimatch goal with
  | [ H : _ |- _ ] => tac H
  end.

Ltac allH tac :=
  match goal with
  | [ H : _ |- _ ] => tac H
  end.

Ltac applyH := multiH ltac:(fun H => apply H).

Example test_applyH : forall P Q R, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros; repeat applyH.
Qed.

Ltac eapplyH := multiH ltac:(fun H => eapply H).

Lemma test_eapplyH : forall T (P Q : T -> Prop) R x y,
    (forall x, P x -> Q y) ->
    (forall x, Q x -> R) ->
    P x -> R.
Proof.
  intros; repeat eapplyH.
Qed.

Ltac rewriteH_fwd := multiH ltac:(fun H => rewrite -> H).
Ltac rewriteH_bwd := multiH ltac:(fun H => rewrite <- H).
Ltac rewriteH_any := multiH ltac:(fun H => rewrite H + rewrite <- H).

Tactic Notation "rewriteH" "->" := rewriteH_fwd.
Tactic Notation "rewriteH" "<-" := rewriteH_bwd.
Tactic Notation "rewriteH" "*" := rewriteH_any.
Tactic Notation "rewriteH" := rewriteH_fwd.

Example test_rewriteH : forall T (w x y z : T),
    x = w -> x = y -> z = y -> w = z.
Proof.
  intros; rewriteH; rewriteH <-; rewriteH ->; reflexivity.
Qed.

Example test_rewriteH_star : forall T (w x y z : T),
    x = w -> x = y -> z = y -> w = z.
Proof.
  intros; do 3 rewriteH *; reflexivity.
Qed.

Ltac require H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    assert H1 as x; [| specialize (H x)]
  end.

Ltac erequire H :=
  match type of H with
  | forall _  : ?H1, _ =>
    let x := fresh in
    evar (x : H1); specialize (H x); subst x
  end.
