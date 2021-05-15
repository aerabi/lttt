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