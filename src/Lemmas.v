Require Import Base.
Require Import BaseProofs.
Require Import ListCtx.
Require Import DeclarativeTypingList.
Require Import OperationalSemantics.

Import DeclarativeTypingList.
Import DeclarativeTyping𝔗𝔄.

Axiom 𝔱subst_type :  forall Γ t t' T T' x,
  type𝔗 (m𝔊.append Γ x T') t T -> type𝔗 Γ t' T' -> type𝔗 Γ (SemanticsBase.𝔱subst t x t') T.

Lemma 𝔱_preservation : forall Γ t t' T, type𝔗 Γ t T -> 𝔱sem t t' -> type𝔗 Γ t' T.
Proof.
  intros. induction H0; inversion H.
  - inversion H2. auto.
  - inversion H2. auto.
  - eapply 𝔱subst_type. inversion H3.  apply H8. apply H5.
  - eapply 𝔱subst_type. apply H8. inversion H7. auto.
  - eapply 𝔱subst_type. apply H9. inversion H7. auto.
Qed.

Axiom 𝔢subst_type : forall Γ Δ1 Δ2 Δ e e' A A' x,
  Δ = m𝔇.mult Δ1 Δ2 -> type𝔄 Γ (m𝔇.append Δ1 x A') e A -> type𝔄 Γ Δ2 e' A' -> type𝔄 Γ Δ (SemanticsBase.𝔢subst e x e') A.

Proposition 𝔢subst_type_empty : forall Γ e e' A A' x,
  type𝔄 Γ (m𝔇.append m𝔇.empty x A') e A -> type𝔄 Γ m𝔇.empty e' A' -> type𝔄 Γ m𝔇.empty (SemanticsBase.𝔢subst e x e') A.
Proof.
  intros. eapply 𝔢subst_type with (Δ1 := m𝔇.empty) (Δ2 := m𝔇.empty); auto.
  - apply H.
  - apply H0.
Qed.

Proposition doubleton_uniqe_paired : forall x1 x2 A1 A2, x1 <> x2 ->
  m𝔇.unique_paired (m𝔇.mult (m𝔇.append m𝔇.empty x2 A2) (m𝔇.append m𝔇.empty x1 A1)).
Proof.
Admitted.

Lemma 𝔢_preservation : forall e e' A, type𝔄 m𝔊.empty m𝔇.empty e A -> 𝔢sem e e' -> type𝔄 m𝔊.empty m𝔇.empty e' A.
Proof.
  intros. induction H0. 
  - inversion H; apply m𝔇.inverse in H0; inversion H0; subst Δ1; subst Δ2; simpl; auto.
  - rename H0 into H'. inversion H; apply m𝔇.inverse in H0; inversion H0; subst Δ1; subst Δ2; simpl; auto.
    eapply 𝔢subst_type_empty; inversion H7. Focus 2. apply m𝔇.inverse in H9. inversion H9. subst Δ1. subst Δ2. apply H16.
    eapply 𝔢subst_type. Focus 3. apply m𝔇.inverse in H9. inversion H9. rewrite -> H17 in H14. apply H14.
    rewrite -> m𝔇.id_r. reflexivity. rewrite -> m𝔇.append_commut. auto. apply doubleton_uniqe_paired. auto.
  - inversion H; apply m𝔇.inverse in H0; inversion H0; subst Δ1; subst Δ2; simpl; auto.
    eapply 𝔢subst_type_empty. Focus 2. apply H6. inversion H4. auto.
  - inversion H; apply m𝔇.inverse in H0; inversion H0; subst Δ1; subst Δ2; simpl; auto.
    eapply 𝔢subst_type_empty. Focus 2. inversion H6. apply H12. apply H7.
  - inversion H; apply m𝔇.inverse in H0; inversion H0; subst Δ1; subst Δ2; simpl; auto.
  - inversion H; apply m𝔇.inverse in H0; inversion H0; subst Δ1; subst Δ2; simpl; auto.
    eapply 𝔢subst_type_empty. apply H9. inversion H8. auto.
  - inversion H; apply m𝔇.inverse in H0; inversion H0; subst Δ1; subst Δ2; simpl; auto.
    eapply 𝔢subst_type_empty. apply H10. inversion H8. auto.
Qed.