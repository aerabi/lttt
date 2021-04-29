Require Import Base.
Require Import DeclarativeTypingList.

Import Base.
Import DeclarativeTypingList.
Import DeclarativeTyping𝔗𝔄.

Lemma contains_𝔗_var : forall Γ x T, m𝔊.contains Γ x T -> Γ ⊩ 𝔱id x | T.
Proof.
  intros. induction H.
  - subst s. apply T𝔗.Var.
  - inversion IHcontains. rewrite -> m𝔊.append_commut_weak. apply T𝔗.Var. auto.
Qed.

Definition x : 𝔵 := 𝔵id 1.
Definition y : 𝔵 := 𝔵id 2.
Definition z : 𝔵 := 𝔵id 3.

Definition f : 𝔵 := 𝔵id 4.
Definition g : 𝔵 := 𝔵id 5.

Definition Γ1 : 𝔊 := m𝔊.append m𝔊.empty x Unit.

Example example_𝔗_duplicate : forall T1 T2,
  (m𝔊.append (m𝔊.append Γ1 f (Unit → T1)) g (Unit → T2)) ⊩ 𝔱pair (𝔱app (𝔱id f) (𝔱id x)) (𝔱app (𝔱id g) (𝔱id x)) | (T1 × T2).
Proof.
  intros. apply T𝔗.𝔗mult_I; eapply T𝔗.𝔗impl_E; apply contains_𝔗_var.
  - apply m𝔊.contains_append_set. eapply m𝔊.contains_append. reflexivity. intros [=].
  - apply m𝔊.contains_append_set. apply m𝔊.contains_append_set. unfold Γ1. eapply m𝔊.contains_append. reflexivity.
    intros [=]. intros [=].
  - eapply m𝔊.contains_append. reflexivity.
  - apply m𝔊.contains_append_set. apply m𝔊.contains_append_set. unfold Γ1. eapply m𝔊.contains_append. reflexivity.
    intros [=]. intros [=].
Qed.
